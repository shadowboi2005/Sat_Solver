#include <bits/stdc++.h>
#include <thread>
#include<mutex>
#include<atomic>

using namespace std;

enum RetVal {
    r_satisfied,
    r_unsatisfied,
    r_normal
};

class cdcl {

    private:
        vector<int> literals;
        vector<vector<int>> clauses;
        int numLiterals;
        int numClauses;
        vector<int> literalFreq;
        vector<int> polarity;
        vector<int> originalLiteralFreq;
        int kappaAntecedent;
        vector<int> literalDecisionLevel;
        vector<int> literalAntecedent;
        int assignedLiteralCount;
        bool alreadyUNSAT;
        int pickCounter;

        int unitPropogate(int);
        void assignLiteral(int,int,int);
        void unassignLiteral(int);
        int literalToVar(int);
        int backtrack(int);
        vector<int>&resolve (vector<int>&,int);
        int pickBranchingVar();
        bool allVarsAssigned();
        void showResult(int);
    public:
        void initialise();
        int getResult();
        void solve();
};

void cdcl::initialise() {
    char c;
    string s;
    
    while (true) {
        cin>>c;
        if (c == 'c') {
            getline(cin,s);
        }
        else {
            cin>>s;
            break;
        }
    }

    cin>>numLiterals;
    cin>>numClauses;
    assignedLiteralCount = 0;
    kappaAntecedent = -1;
    pickCounter = 0;
    alreadyUNSAT = false;

    literals.clear();
    literals.resize(numLiterals,-1);
    literalFreq.clear();
    literalFreq.resize(numLiterals,0);
    literalAntecedent.clear();
    literalAntecedent.resize(numLiterals,-1);
    polarity.clear();
    polarity.resize(numLiterals,0);
    literalDecisionLevel.clear();
    literalDecisionLevel.resize(numLiterals,-1);
    clauses.clear();
    clauses.resize(numClauses);

    int literal;
    int literalCountInClause = 0;
    for (int i=0; i<numClauses; i++) {
        literalCountInClause = 0;
        while (true) {

            cin>>literal;
            if (literal > 0) {
                clauses[i].push_back(literal);
                literalFreq[literal - 1]++;
                polarity[literal - 1]++;
                literalCountInClause++;
            }
            else if (literal < 0) {
                clauses[i].push_back(literal);
                literalFreq[-literal-1]++;
                polarity[-literal-1]--;
                literalCountInClause++;
            }
            else {
                if (literalCountInClause == 0) {
                    alreadyUNSAT = true;
                }
                break;
            }

        }
    }
    originalLiteralFreq = literalFreq;
    // cout<<"Initialisation over, input taken, starting solver!\n";

}

void cdcl::solve() {
    
    int result = getResult();
    showResult(result);

}

int cdcl::getResult() {

    int decisionLevel = 0;
    if (alreadyUNSAT) {
        return RetVal::r_unsatisfied;
    }
    int unitRes = unitPropogate(decisionLevel);
    if (unitRes == RetVal::r_unsatisfied) {
        return unitRes;
    }

    while (!allVarsAssigned()) {

        int pickedVar = pickBranchingVar();
        decisionLevel++;
        assignLiteral(pickedVar,decisionLevel,-1);

        while (true) {
    
            unitRes = unitPropogate(decisionLevel);
            if (unitRes == r_unsatisfied) {
                if (decisionLevel == 0) {
                    return RetVal::r_unsatisfied;
                }
                decisionLevel = backtrack(decisionLevel);
            }
            else {
                break;
            }

        }

    }
    return RetVal::r_satisfied;

}

int cdcl::unitPropogate(int decisionLevel) {

    atomic<bool> conflictFound(false);
    atomic<bool> unitClauseFound(false);
    int conflictingVariable = -1;
    int numThreads = thread::hardware_concurrency();
    vector<thread> threads;
    mutex mtx;

    auto worker = [&](int start, int end) {
        for (int i = start; i < end; i++) {
            if (conflictFound.load() || unitClauseFound.load()) {
                return;
            }
            int falseCount = 0;
            int unsetCount = 0;
            bool satisfiedFlag = false;
            int lastUnsetLiteral = -1;
            for (int j = 0; j < clauses[i].size(); j++) {
                int literalIndex = literalToVar(clauses[i][j]);
                if (literals[literalIndex] == -1) {
                    unsetCount++;
                    lastUnsetLiteral = j;
                } else if ((literals[literalIndex] == 0 && clauses[i][j] > 0) || (literals[literalIndex] == 1 && clauses[i][j] < 0)) {
                    falseCount++;
                } else {
                    satisfiedFlag = true;
                    break;
                }
            }
            if (satisfiedFlag) {
                continue;
            }
            if (unsetCount == 1) {
                {
                    lock_guard<mutex> lock(mtx);
                    if (!conflictFound.load()) {
                        assignLiteral(clauses[i][lastUnsetLiteral], decisionLevel, i);
                    }
                }
                unitClauseFound.store(true);
            } else if (falseCount == clauses[i].size()) {
                {
                    lock_guard<mutex> lock(mtx);
                    conflictFound.store(true);
                    conflictingVariable = i;
                }
                return;
            }
        }
    };

    do {
        unitClauseFound.store(false);
        threads.clear();
        int chunkSize = (clauses.size() + numThreads - 1) / numThreads;
        for (int i = 0; i < numThreads; i++) {
            int start = i * chunkSize;
            int end = min(start + chunkSize, int(clauses.size()));
            threads.emplace_back(worker, start, end);
        }
        for (auto& t: threads) {
            t.join();
        }
    } while (unitClauseFound.load());

    if (conflictFound.load()) {
        kappaAntecedent = conflictingVariable;
        return r_unsatisfied;
    }
    kappaAntecedent = -1;
    return r_normal;

}

int cdcl::literalToVar(int lit) {
    if (lit > 0) {
        return lit-1;
    }
    else {
        return -lit-1;
    }
} 

void cdcl::assignLiteral(int variable, int decisionLevel, int antecedent) {

    int lit = literalToVar(variable);
    if (variable > 0) {
        literals[lit] = 1;
    }
    else {
        literals[lit] = 0;
    }
    literalAntecedent[lit] = antecedent;
    literalDecisionLevel[lit] = decisionLevel;
    literalFreq[lit] = -1;
    assignedLiteralCount++;

}

int cdcl::pickBranchingVar() {
    
    int mostFreq = 0;
    for (int i=1; i<literalFreq.size(); i++) {
        if (literalFreq[i] > literalFreq[mostFreq]) {
            mostFreq = i;
        }
    }
    if (polarity[mostFreq] >= 0) {
        return mostFreq+1;
    }
    else {
        return -mostFreq-1;
    }

}

int cdcl::backtrack(int decisionLevel) {

    vector<int> learntClauses = clauses[kappaAntecedent];
    int conflictDecisionLevel = decisionLevel;
    int thisLevelCount = 0;              
    int resolverLiteral; 
    int literal;         

    while (true) {

        thisLevelCount = 0;
        for (int i=0; i<learntClauses.size(); i++) {
            literal = literalToVar(learntClauses[i]);
            if (literalDecisionLevel[literal] == decisionLevel) {
                thisLevelCount++;
            }
            if (literalDecisionLevel[literal] == decisionLevel && literalAntecedent[literal] != -1) {
                resolverLiteral = literal;
            }
        }
        if (thisLevelCount == 1) {
            break;
        }
        else {
            learntClauses = resolve(learntClauses,resolverLiteral);
        }

    }
    clauses.push_back(learntClauses);

    for (int i=0; i<learntClauses.size(); i++) {
        int lit = literalToVar(learntClauses[i]);
        if (learntClauses[i] > 0) {
            polarity[lit]++;
        }
        else {
            polarity[lit]--;
        }
        if (literalFreq[lit] != -1) {
            literalFreq[lit]++;
        }
        originalLiteralFreq[lit]++;
    }
    numClauses++;
    int backtrackedDL = 0;

    for (int i=0; i<learntClauses.size(); i++) {
        int lit = literalToVar(learntClauses[i]);
        int litDL = literalDecisionLevel[lit];
        if (litDL != conflictDecisionLevel && litDL > backtrackedDL) {
            backtrackedDL = litDL;
        }
    }

    for (int i=0; i<literals.size(); i++) {
        if (literalDecisionLevel[i] > backtrackedDL) {
            unassignLiteral(i);
        }
    }

    return backtrackedDL;

}

void cdcl::unassignLiteral(int lit) {
    literals[lit] = -1;
    literalDecisionLevel[lit] = -1;
    literalFreq[lit] = originalLiteralFreq[lit];
    literalAntecedent[lit] = -1;
    assignedLiteralCount--;
}

bool cdcl::allVarsAssigned () {
    return (numLiterals == assignedLiteralCount); 
}

vector<int>& cdcl::resolve(vector<int>& clause, int resolutionLiteral) {

    vector<int> otherClause = clauses[literalAntecedent[resolutionLiteral]];
    clause.insert(clause.end(),otherClause.begin(),otherClause.end());
    for (int i=0; i<clause.size(); i++) {
        if (clause[i] == resolutionLiteral + 1 || clause[i] == -resolutionLiteral-1) {
            clause.erase(clause.begin() + i);
            i--;
        }
    }
    sort(clause.begin(), clause.end());
    clause.erase(unique(clause.begin(),clause.end()),clause.end());
    return clause;

}

void cdcl::showResult(int res) {
    if (res == RetVal::r_satisfied) {
        cout<<"SAT"<<" | ";
        for (int i=0; i<literals.size(); i++) {
            if (literals[i] != -1) {
                if (literals[i] > 0) {
                    cout<<(i+1)<<" ";
                }
                else {
                    cout<<"-"<<(i+1)<<" ";
                }
            }
            else {
                cout<<(i+1)<<" ";
            }
        }
        cout<<" 0"<<endl;
    }
    else {
        cout<<"UNSAT"<<endl;
    }

} 

int main() {
    cdcl solver;
    solver.initialise();
    solver.solve();
}