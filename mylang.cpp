#include "KaleidoscopeJIT.hpp"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/StandardInstrumentations.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/Reassociate.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <vector>

using namespace llvm;
using namespace llvm::orc;








enum Token{

    tok_eof = -1,
    tok_def = -2,
    tok_extern = -3,
    tok_identifier = -4,
    tok_number = -5,

};


class ExprAST;
class NumberExprAST;
class VariableExprAST;
class BinaryExprAST;
class CallExprAST;
class PrototypeAST;
class FunctionAST;

static std::unique_ptr<ExprAST> ParseNumberExpr();
static std::unique_ptr<ExprAST> ParsePrimary();
static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExpPrec, std::unique_ptr<ExprAST> LHS);
static std::unique_ptr<ExprAST> ParseExpression();
static std::unique_ptr<ExprAST> ParseParenExpr();
static std::unique_ptr<ExprAST> ParseIdentifier();
std::unique_ptr<ExprAST> LogError(const char *Str);

static int GetTokPrecedence();

static std::unique_ptr<PrototypeAST> ParsePrototype();

static std::string IdentifierStr; //when identifies idnetifier name
static double NumVal;//When identifies a number


static int gettok(){

    static int LastChar = ' ';

    //Skips the spaces
    while(isspace(LastChar)){
        LastChar = getchar();
    }

    //Parse the indentifier 
    if(isalpha(LastChar)){
        //coerce the int to string
        IdentifierStr = LastChar;
        while(isalnum((LastChar = getchar()))){
            IdentifierStr += LastChar;
        }

        if(IdentifierStr == "def"){
            return tok_def;
        }
        else if(IdentifierStr == "extern"){
            return tok_extern;
        }
        return tok_identifier;
    }



    //digit.digit.... does not work
    if(isdigit(LastChar) || LastChar == '.'){
        std::string Numstr;
        do{
        Numstr += LastChar;
        LastChar = getchar();
        }while (isdigit(LastChar) || LastChar == '.');

        NumVal = strtod(Numstr.c_str(), 0);
        return tok_number;
    }
    //handling comments
    if(LastChar == '#'){
        do{
        LastChar = getchar();
        }while (LastChar != EOF && LastChar!= '\n' && LastChar != '\r');

        //If not end of file we want to get the next token
        if(LastChar != EOF){
            return gettok();
        }
    }

    if(LastChar == EOF){
        return tok_eof;
    }

    int ThisChar = LastChar;
    LastChar = getchar();
    return ThisChar;    

}

static std::unique_ptr<LLVMContext> TheContext;
static std::unique_ptr<Module> TheModule;
static std::unique_ptr<IRBuilder<>> Builder;
static std::map<std::string, Value *> NamedValues;
static std::unique_ptr<KaleidoscopeJIT> TheJIT;
static std::unique_ptr<FunctionPassManager> TheFPM;
static std::unique_ptr<LoopAnalysisManager> TheLAM;
static std::unique_ptr<FunctionAnalysisManager> TheFAM;
static std::unique_ptr<CGSCCAnalysisManager> TheCGAM;
static std::unique_ptr<ModuleAnalysisManager> TheMAM;
static std::unique_ptr<PassInstrumentationCallbacks> ThePIC;
static std::unique_ptr<StandardInstrumentations> TheSI;
static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;
static ExitOnError ExitOnErr;


class ExprAST{

public:
    //to put it empty and then subclasses can have their own implementation
    virtual ~ExprAST(){

    }
    virtual Value *codegen() = 0;

};

//make it public that NumberExprAST publicly derives ExprAST
//if it is not made public you are not allowed to do casting
class NumberExprAST : public ExprAST{

    double Val;
    public:
        NumberExprAST(double Val): Val(Val) {}
        virtual Value *codegen();

};

Value *NumberExprAST::codegen() {
  return ConstantFP::get(Type::getDoubleTy(*TheContext), Val);
}



class VariableExprAST : public ExprAST{
    std::string Name;
    public:
        VariableExprAST(const std::string &Name): Name(Name) {}
        virtual Value *codegen();
};

Value *VariableExprAST::codegen(){
  Value *V = NamedValues[Name];
  if(!V){
    LogError("No variable name");
  }
  return V;
}

class BinaryExprAST : public ExprAST{
    char Op;
    std::unique_ptr<ExprAST> LHS, RHS;

    public:
        BinaryExprAST(char Op,
                        std::unique_ptr<ExprAST> LHS, 
                        std::unique_ptr<ExprAST> RHS): 
                        Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}

        virtual Value *codegen();
};

Value *BinaryExprAST::codegen(){
  Value *L = LHS->codegen();
  Value *R = RHS->codegen();

  if(!L || !R){
    return nullptr;
  }

    switch (Op) {
    case '+':
      return Builder->CreateFAdd(L, R, "addtmp");
    case '-':
      return Builder->CreateFSub(L, R, "subtmp");
    case '*':
      return Builder->CreateFMul(L, R, "multmp");
    case '<':
      L = Builder->CreateFCmpULT(L, R, "cmptmp");
      return Builder->CreateUIToFP(L, Type::getDoubleTy(*TheContext), "booltmp");
    default:
      LogError("invalid binary operator");
      return nullptr;
  }

}

class CallExprAST : public ExprAST{
    std::string Callee; //the name of the function
    std::vector<std::unique_ptr <ExprAST> > Args; //the args of the function

    public:
        CallExprAST(const std::string &Callee, 
                    std::vector<std::unique_ptr <ExprAST> > Args):
                    Callee (Callee), Args(std::move(Args)){}

        virtual Value *codegen();

};

Value *CallExprAST::codegen(){

  Function *CalleeF = TheModule->getFunction(Callee);
  if(!CalleeF){
    LogError("Unknown function referenced");
    return nullptr;
  }

  if(CalleeF->arg_size() != Args.size()){
    LogError("Incorrect number of arguments size");
    return nullptr;
  }

  std::vector<Value *> ArgsV;
  for (unsigned i = 0, e = Args.size(); i != e; ++i) {
      ArgsV.push_back(Args[i]->codegen());
      if (!ArgsV.back())
          return nullptr;
  }

  return Builder->CreateCall(CalleeF, ArgsV, "calltmp");

}

//proto is name of the function and its arguments lists
class PrototypeAST {
  std::string Name;
  std::vector<std::string> Args;

public:
  PrototypeAST(const std::string &Name, std::vector<std::string> Args)
    : Name(Name), Args(std::move(Args)) {}

  const std::string &getName() const { return Name; }
  virtual Function *codegen();

};

Function *PrototypeAST::codegen(){
  //type of each parameter
  std::vector<Type*> Doubles(Args.size(), Type::getDoubleTy(*TheContext));

  FunctionType *FT =
    FunctionType::get(Type::getDoubleTy(*TheContext), Doubles, false);
  
  Function *F =
    Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get() );

  unsigned Idx = 0;
  for(auto &arg : F->args()){
    arg.setName(Args[Idx++ ]);
  }

  return F;
}

//the proto + body
class FunctionAST {
  std::unique_ptr<PrototypeAST> Proto;
  std::unique_ptr<ExprAST> Body;

public:
  FunctionAST(std::unique_ptr<PrototypeAST> Proto,
              std::unique_ptr<ExprAST> Body)
    : Proto(std::move(Proto)), Body(std::move(Body)) {}
    virtual Function *codegen();

};

Function *FunctionAST::codegen(){
  Function *TheFunction = TheModule->getFunction(Proto->getName());
  if(!TheFunction){
    TheFunction = Proto->codegen();
  }
  if(!TheFunction){
    return nullptr;
  }
  //if the function has body it is a problem
  if(!TheFunction->empty()){
    LogError("Function can not be redefined");
    return nullptr;
  }

  BasicBlock *BB = BasicBlock::Create(*TheContext, "entry", TheFunction);
  Builder->SetInsertPoint(BB);

  NamedValues.clear();
  for(auto &Arg : TheFunction->args()){
    NamedValues[Arg.getName().str()] = &Arg; 
  }

  Value *Retval = Body->codegen();
  if(Retval){
        Builder->CreateRet(Retval);

    // Validate the generated code, checking for consistency.
    verifyFunction(*TheFunction);

    // Run the optimizer on the function.
    TheFPM->run(*TheFunction, *TheFAM);

    return TheFunction;
  }
  TheFunction->eraseFromParent();
  return nullptr;

}


static int CurTok;
static int getNextToken() {
  return CurTok = gettok();
}

std::unique_ptr<ExprAST> LogError(const char *Str) {
  fprintf(stderr, "Error: %s\n", Str);
  return nullptr;
}
std::unique_ptr<PrototypeAST> LogErrorP(const char *Str) {
  LogError(Str);
  return nullptr;
}

static std::unique_ptr<ExprAST> ParseNumberExpr(){
    auto Result = std::make_unique<NumberExprAST>(NumVal);
    getNextToken();
    return std::move(Result);

}

static std::unique_ptr<ExprAST> ParsePrimary(){
    if(CurTok == tok_identifier){
        return ParseIdentifier();
    }
    else if(CurTok == tok_number){
        return ParseNumberExpr();
    }
    else if(CurTok == '('){
        return ParseParenExpr();
    }
    return LogError("unknown token when expecting an expression");;
}
        

static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExpPrec, std::unique_ptr<ExprAST> LHS){

    while(true){
        int TokPrec = GetTokPrecedence();
        if(TokPrec < ExpPrec){
                return (LHS);
        }
        else{
            int BinOp = CurTok;
            getNextToken();
            auto RHS = ParsePrimary();
            if(RHS){
                int NextPrec = GetTokPrecedence();
                if (TokPrec < NextPrec){
                    RHS = ParseBinOpRHS(TokPrec+1, std::move(RHS));
                    
                }
                LHS = std::make_unique<BinaryExprAST>(BinOp, std::move(LHS),
                    std::move(RHS));
            }
            else{
                return nullptr;
            }
        }

    }

}


static std::unique_ptr<ExprAST> ParseExpression() {
    auto LHS = ParsePrimary();
    if(!LHS){
        return nullptr;
    }

    return ParseBinOpRHS(0, std::move(LHS));    
}


static std::unique_ptr<ExprAST> ParseParenExpr(){
  getNextToken(); // eat (.
  auto V = ParseExpression();
  if (!V)
    return nullptr;

  if (CurTok != ')')
    return LogError("expected ')'");
  getNextToken(); // eat ).
  return V;
}


static std::unique_ptr<ExprAST> ParseIdentifier(){
    std::string IdName = IdentifierStr;

    getNextToken();

    if(CurTok == '('){
        getNextToken();
        std::vector<std::unique_ptr<ExprAST>> Args;
        while(true){
            auto Arg = ParseExpression();
            if(Arg){
                Args.push_back(std::move(Arg));
            }
            else{
                return nullptr;
            }
            if(CurTok == ')'){
                getNextToken();
                break;
            }
            else if(CurTok == ','){
                getNextToken();
            }
            else{
                return LogError("expected ')'");
            }
        }
        return std::make_unique<CallExprAST>(IdName, std::move(Args)); 
    }
    else{
        return std::make_unique<VariableExprAST>(IdName);
    }
}



static std::map<char, int> Binopprecedence;

static int GetTokPrecedence(){
    switch (CurTok)
    {
    case '<':
    case '>':
        return 10;
    case '-':
    case '+':
        return 20;
    case '*':
    case '/':
        return 40;
    default:
        return -1;
    }
}





static std::unique_ptr<PrototypeAST> ParsePrototype() {
  if (CurTok != tok_identifier)
    return LogErrorP("Expected function name in prototype");

  std::string FnName = IdentifierStr;
  getNextToken();

  if (CurTok != '(')
    return LogErrorP("Expected '(' in prototype");

  // Read the list of argument names.
  std::vector<std::string> ArgNames;
  while (getNextToken() == tok_identifier){
    ArgNames.push_back(IdentifierStr);
  }
  if (CurTok != ')')
    return LogErrorP("Expected ')' in prototype");

  // success.
  getNextToken();  // eat ')'.

  return std::make_unique<PrototypeAST>(FnName, std::move(ArgNames));
}

static std::unique_ptr<FunctionAST> ParseDefinition() {
  getNextToken();  // eat def.
  auto Proto = ParsePrototype();
  if (!Proto) return nullptr;
  auto E = ParseExpression();

  if (E)
    return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
  else
  return nullptr;
}

static std::unique_ptr<PrototypeAST> ParseExtern() {
  getNextToken();  // eat extern.
  return ParsePrototype();
}

static std::unique_ptr<FunctionAST> ParseTopLevelExpr() {
  if (auto E = ParseExpression()) {
    // Make an anonymous proto.
    auto Proto = std::make_unique<PrototypeAST>("", std::vector<std::string>());
    return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
  }
  return nullptr;
}

static void InitializeModule() {
  // Open a new context and module.
  TheContext = std::make_unique<LLVMContext>();
  TheModule = std::make_unique<Module>("my cool jit", *TheContext);

  // Create a new builder for the module.
  Builder = std::make_unique<IRBuilder<>>(*TheContext);
}

static void HandleDefinition() {
  if (auto FnAST = ParseDefinition()) {
    if (auto *FnIR = FnAST->codegen()) {
      fprintf(stderr, "Read function definition:");
      FnIR->print(errs());
      fprintf(stderr, "\n");
    }
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

static void HandleExtern() {
  if (auto ProtoAST = ParseExtern()) {
    if (auto *FnIR = ProtoAST->codegen()) {
      fprintf(stderr, "Read extern: ");
      FnIR->print(errs());
      fprintf(stderr, "\n");
    }
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

static void HandleTopLevelExpression() {
  // Evaluate a top-level expression into an anonymous function.
  if (auto FnAST = ParseTopLevelExpr()) {
    if (auto *FnIR = FnAST->codegen()) {
      fprintf(stderr, "Read top-level expression:");
      FnIR->print(errs());
      fprintf(stderr, "\n");

      // Remove the anonymous expression.
      FnIR->eraseFromParent();
    }
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

/// top ::= definition | external | expression | ';'
static void MainLoop() {
  while (true) {
    fprintf(stderr, "ready> ");
    switch (CurTok) {
    case tok_eof:
      return;
    case ';': // ignore top-level semicolons.
      getNextToken();
      break;
    case tok_def:
      HandleDefinition();
      break;
    case tok_extern:
      HandleExtern();
      break;
    default:
      HandleTopLevelExpression();
      break;
    }
  }
}

static void InitializeModuleAndManagers() {
  // Open a new context and module.
  TheContext = std::make_unique<LLVMContext>();
  TheModule = std::make_unique<Module>("KaleidoscopeJIT", *TheContext);
  TheModule->setDataLayout(TheJIT->getDataLayout());

  // Create a new builder for the module.
  Builder = std::make_unique<IRBuilder<>>(*TheContext);

  // Create new pass and analysis managers.
  TheFPM = std::make_unique<FunctionPassManager>();
  TheLAM = std::make_unique<LoopAnalysisManager>();
  TheFAM = std::make_unique<FunctionAnalysisManager>();
  TheCGAM = std::make_unique<CGSCCAnalysisManager>();
  TheMAM = std::make_unique<ModuleAnalysisManager>();
  ThePIC = std::make_unique<PassInstrumentationCallbacks>();
  TheSI = std::make_unique<StandardInstrumentations>(*TheContext,
                                                     /*DebugLogging*/ true);
  TheSI->registerCallbacks(*ThePIC, TheMAM.get());

  // Add transform passes.
  // Do simple "peephole" optimizations and bit-twiddling optzns.
  TheFPM->addPass(InstCombinePass());
  // Reassociate expressions.
  TheFPM->addPass(ReassociatePass());
  // Eliminate Common SubExpressions.
  TheFPM->addPass(GVNPass());
  // Simplify the control flow graph (deleting unreachable blocks, etc).
  TheFPM->addPass(SimplifyCFGPass());

  // Register analysis passes used in these transform passes.
  PassBuilder PB;
  PB.registerModuleAnalyses(*TheMAM);
  PB.registerFunctionAnalyses(*TheFAM);
  PB.crossRegisterProxies(*TheLAM, *TheFAM, *TheCGAM, *TheMAM);
}


int main() {
  InitializeNativeTarget();
  InitializeNativeTargetAsmPrinter();
  InitializeNativeTargetAsmParser();
  // Prime the first token.
 // Prime the first token.
  fprintf(stderr, "ready> ");
  getNextToken();

  // Make the module, which holds all the code.
  TheJIT = ExitOnErr(KaleidoscopeJIT::Create());

  InitializeModuleAndManagers();

  // Run the main "interpreter loop" now.
  MainLoop();

  // Print out all of the generated code.
  TheModule->print(errs(), nullptr);

  return 0;
}