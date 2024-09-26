#include <bits/stdc++.h>
using namespace std;

/*

The Naive SAT Solver algorithm is far too slow, thus there is a better algorithm for SAT solving called DPLL
Davis–Putnam–Logemann–Loveland (DPLL) Algorithm:
* First perform unit propogation to get rid of unit clauses (clauses that have only one literal)
* Then, decide the value of some variable and check if the formula becomes SAT (by for example, recursively calling DPLL)
* If it does, return the assignment
* If not, then change the value of that variable 

*/

#define UNDEFINED -1
#define TRUE 1
#define FALSE 0

class dpll {
    private:
    uint numVariables;
    uint numClauses;
    vector<vector<int>> clauses;
    bool unitProp (vector<int>& partialModel);
    bool doPll (vector<int>& partialModel);
    
    public:
    vector<int> finalModel;
    void getInput ();
    bool solve();

};



void dpll::getInput () {

    char c = cin.get(); // CNF comments
    while (c == 'c') {
        while (c != '\n') {
            c = cin.get();
        }
        c = cin.get();
    }
    string t;
    cin>>t;

    cin>>numVariables;
    cin>>numClauses;
    for (uint i=0; i<numVariables+1; i++) {
        finalModel.push_back(UNDEFINED);
    }
    for (uint i=0; i<numClauses; i++) {
        vector<int> a;
        int c;
        cin>>c;
        while (c != 0) {
            a.push_back(c);
            cin>>c;
        }
        // a.value = UNDEFINED;
        // a.size = a.elements.size();
        clauses.push_back(a);
    }
}

bool dpll::unitProp (vector<int>& partialModel) {
/*
}


Implement unit propogation!
while (true) {

    if (there exists some clause C, such that there is only one undecided variable in C) {
        decide the variable so as to make C true; (i.e. if C is x, then set x to true, else if C is -x, set x to false)
    }
    if (some clause becomes false) {
        return false;
    }
    if (no such clause exists) {
        break;
    }

}

*/
while (true)
{
    bool clause_exist = false;
    for(auto& clause: clauses){
        int num_of_unasgn_var = 0;
        int unasgn_literal = 0;
        bool clause_satisfied = false;
        for(auto& literal : clause){
            int varnum = abs(literal);
            //cout<< literal<<","<<partialModel[abs(literal)]<<endl;
            if(partialModel[varnum] == UNDEFINED){
                num_of_unasgn_var++;
                unasgn_literal = literal;
            }

            int not_not_there = (literal > 0)? 1:0; //-x or x
            if(partialModel[varnum] == not_not_there){// check if it true or not
                clause_satisfied = true;
                break;
            }
        }
        if(!clause_satisfied && num_of_unasgn_var==0){
            return false; // backtrack now
        }
        if(!clause_satisfied && num_of_unasgn_var ==1){
            partialModel[abs(unasgn_literal)] = (unasgn_literal > 0)? 1:0;
            clause_exist = true;
            break;
        }
    }
    if(!clause_exist){
        break;
    }
}
return true;


}

bool dpll::doPll (vector<int>& partialModel) {

/*

Implement the dpll algorithm
unitProp(partialModel)
if (formula is SAT) {
    finalModel = partialModel;
    return true;
}
else {
    if (there exists variable x, partialModel[x] == UNDECIDED) {
        posMod = partialModel;
        posMod[x] = 1;
        negMod = partialModel;
        negMod[x] = 0;
        return (doPll(posMod) || doPll(negMod));
    }
    else {
        return false;
    }
}

*/

if(!unitProp(partialModel)){
    return false;
}
//cout<<"reached here\n";
bool form_is_sat = true;
for(auto& clause :clauses){
    bool clause_Val = false;
    for(auto& literal : clause){
        int parity = (literal > 0)? 1:0;
        if(partialModel[abs(literal)] == parity){
            clause_Val = true;
            break;
        }
    }
    if(!clause_Val){
        form_is_sat = false;
        break;
    }
}
if(form_is_sat){
    finalModel = partialModel;
    return true;
}
for(int i = 1;i<numVariables +1;i++){
    if(partialModel[i] == UNDEFINED){
        vector<int> var_true_model(partialModel);
        vector<int> var_false_model(partialModel);
        var_true_model[i] = 1;
        var_false_model[i] = 0;
        /*for (int i=1; i<var_true_model.size(); i++) {
            cout<<i<<" : "<<var_true_model[i]<<endl;
        } */
        if(doPll(var_true_model) || doPll(var_false_model)){
            return true;
        } 
        return false;
    }
}
return false; 
}

bool dpll::solve() {
    vector<int> m(numVariables+1,UNDEFINED);
    return doPll(m);
}

int main () {
    
    dpll d;
    d.getInput();

    if (d.solve()) {
        cout<<"TRUE\n";
        for (int i=1; i<d.finalModel.size(); i++) {
            cout<<i<<" : "<<d.finalModel[i]<<endl;
        }
    }
    else {
        cout<<"UNSAT\n";
    }
}