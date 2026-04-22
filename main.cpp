#include <bits/stdc++.h>
using namespace std;

// We implement symbolic differentiation per problem spec.
// Expression grammar: +,-,*,/, parentheses, terms a*x^b*sin^c x * cos^d x.
// Internally, represent Poly as vector of Terms, Frac as p/q of Poly.

struct Term {
    long long a; // coefficient
    int b, c, d; // exponents of x, sinx, cosx
    Term(long long a_=0,int b_=0,int c_=0,int d_=0):a(a_),b(b_),c(c_),d(d_){}
};

static inline bool term_key_gt(const Term &x, const Term &y){
    if(x.b!=y.b) return x.b>y.b;
    if(x.c!=y.c) return x.c>y.c;
    return x.d>y.d;
}

struct Poly{
    vector<Term> v;
    Poly(){}
    Poly(const vector<Term>&vv):v(vv){}
    void simplify(){
        // remove zeros, sort by key, merge like terms
        vector<Term> tmp;
        for(auto &t:v) if(t.a!=0) tmp.push_back(t);
        sort(tmp.begin(), tmp.end(), [](const Term&x,const Term&y){
            if(x.b!=y.b) return x.b>y.b;
            if(x.c!=y.c) return x.c>y.c;
            return x.d>y.d;
        });
        vector<Term> res;
        for(auto &t: tmp){
            if(res.empty() || res.back().b!=t.b || res.back().c!=t.c || res.back().d!=t.d){
                res.push_back(t);
            }else{
                res.back().a += t.a;
                if(res.back().a==0){ res.pop_back(); }
            }
        }
        v.swap(res);
    }
    Poly operator+(const Poly&o)const{ Poly r; r.v.reserve(v.size()+o.v.size()); r.v.insert(r.v.end(), v.begin(), v.end()); r.v.insert(r.v.end(), o.v.begin(), o.v.end()); r.simplify(); return r; }
    Poly operator-(const Poly&o)const{ Poly r; r.v.reserve(v.size()+o.v.size()); r.v.insert(r.v.end(), v.begin(), v.end()); for(auto t:o.v){ t.a=-t.a; r.v.push_back(t);} r.simplify(); return r; }
    Poly operator*(const Poly&o)const{
        Poly r; r.v.reserve(v.size()*o.v.size());
        for(const auto &x:v){
            for(const auto &y:o.v){
                long long a = x.a * y.a;
                int b = x.b + y.b;
                int c = x.c + y.c;
                int d = x.d + y.d;
                if(a!=0) r.v.emplace_back(a,b,c,d);
            }
        }
        r.simplify();
        return r;
    }
    Poly derivate() const{
        // derivative of term a*x^b*sin^c*cos^d is sum of up to 3 terms:
        // a*b*x^{b-1}*sin^c*cos^d + a*c*x^b*sin^{c-1}*cos^{d+1} + a*(-d)*x^b*sin^{c+1}*cos^{d-1}
        Poly res; 
        for(const auto &t: v){
            if(t.b>0){ res.v.emplace_back(t.a * (long long)t.b, t.b-1, t.c, t.d); }
            if(t.c>0){ res.v.emplace_back(t.a * (long long)t.c, t.b, t.c-1, t.d+1); }
            if(t.d>0){ res.v.emplace_back(-t.a * (long long)t.d, t.b, t.c+1, t.d-1); }
        }
        res.simplify();
        return res;
    }
    bool is_zero() const { return v.empty(); }
};

struct Frac{
    Poly p,q; // p/q
    Frac(){}
    Frac(long long x){ p=Poly({Term(x,0,0,0)}); q=Poly({Term(1,0,0,0)}); }
    Frac(const Poly&pp,const Poly&qq){ p=pp; q=qq; }
    static Frac fromTerm(const Term&t){
        Poly pp; if(t.a!=0) pp = Poly({t}); else pp = Poly();
        Poly qq({Term(1,0,0,0)});
        return Frac(pp, qq);
    }
    Frac operator+(const Frac&o)const{ Poly np = p*o.q + o.p*q; Poly nq = q*o.q; return Frac(np,nq); }
    Frac operator-(const Frac&o)const{ Poly np = p*o.q - o.p*q; Poly nq = q*o.q; return Frac(np,nq); }
    Frac operator*(const Frac&o)const{ Poly np = p*o.p; Poly nq = q*o.q; return Frac(np,nq); }
    Frac operator/(const Frac&o)const{ Poly np = p*o.q; Poly nq = q*o.p; return Frac(np,nq); }
    Frac derivate() const{ Poly np = p.derivate()*q - q.derivate()*p; Poly nq = q*q; return Frac(np,nq); }
};

// Output formatting per spec
static void print_poly_inner(const Poly &P){
    if(P.v.empty()){ cout<<"0"; return; }
    bool first=true;
    for(const auto &t:P.v){
        long long coeff = t.a;
        bool neg = coeff < 0;
        long long abscoeff = llabs(coeff);
        bool is_const = (t.b==0 && t.c==0 && t.d==0);
        if(first){
            if(neg) cout<<"-";
        }else{
            cout<<(neg?"-":"+");
        }
        if(is_const){
            cout<<abscoeff;
        }else{
            if(abscoeff!=1) cout<<abscoeff;
            if(t.b){ cout<<"x"; if(t.b!=1) cout<<"^"<<t.b; }
            if(t.c){ cout<<"sin"; if(t.c!=1) cout<<"^"<<t.c; cout<<"x"; }
            if(t.d){ cout<<"cos"; if(t.d!=1) cout<<"^"<<t.d; cout<<"x"; }
        }
        first=false;
    }
}

static void print_frac(const Frac &F){
    // special rules: if numerator zero -> print 0; if denominator == 1 -> print numerator only
    if(F.p.v.empty()){ cout<<"0\n"; return; }
    // check denom == 1
    bool denom_one = (F.q.v.size()==1 && F.q.v[0].a==1 && F.q.v[0].b==0 && F.q.v[0].c==0 && F.q.v[0].d==0);
    if(denom_one){ print_poly_inner(F.p); cout<<"\n"; return; }
    // else (s1)/(s2), with parentheses only if multiple terms
    bool p_multi = (F.p.v.size()>1);
    bool q_multi = (F.q.v.size()>1);
    if(p_multi) cout<<"("; print_poly_inner(F.p); if(p_multi) cout<<")";
    cout<<"/";
    if(q_multi) cout<<"("; print_poly_inner(F.q); if(q_multi) cout<<")";
    cout<<"\n";
}

// Parsing
struct Parser{
    string s; int n; int pos;
    Parser(const string &str):s(str),n((int)str.size()),pos(0){}

    static bool isdigitc(char c){ return c>='0'&&c<='9'; }

    // Parse integer with optional sign, default to +-1 if no digits present based on sign
    long long parse_number_default_one(int l, int r){
        // s[l:r)
        bool neg=false; int i=l;
        if(i<r && s[i]=='-'){ neg=true; i++; }
        long long val=0; bool has=false;
        while(i<r && isdigitc(s[i])){ has=true; val = val*10 + (s[i]-'0'); i++; }
        if(!has) val=1; if(neg) val=-val; return val;
    }

    Term parse_term_range(int l, int r){
        // piece string s[l:r), parse a*x^b*sin^c x * cos^d x. No '*' chars in input formatting, terms are concatenated.
        long long a=0; int b=0,c=0,d=0; // a default 0 means need decide via digits presence
        // find occurrences
        // scan for x not in sinx/cosx: we treat occurrences of 'x' but need avoid the x in sinx/cosx; actual tokens are 'x', 'sinx', 'cosx'
        // We'll scan sequentially, consuming patterns.
        int i=l;
        // coefficient (possibly signed number at start)
        bool neg=false; if(i<r && (s[i]=='+'||s[i]=='-')){ neg = (s[i]=='-'); i++; }
        long long coeff=0; bool hasnum=false;
        while(i<r && isdigitc(s[i])){ hasnum=true; coeff = coeff*10 + (s[i]-'0'); i++; }
        if(!hasnum) coeff=1; if(neg) coeff=-coeff; a=coeff;
        while(i<r){
            if(i+3<=r && s.compare(i,3,"sin")==0){
                i+=3; int exp=1; if(i<r && s[i]=='^'){ i++; int e=0; bool ok=false; while(i<r && isdigitc(s[i])){ ok=true; e=e*10+(s[i]-'0'); i++; } if(ok) exp=e; }
                if(i<r && s[i]=='x') i++; // consume the trailing x
                c += exp;
            }else if(i+3<=r && s.compare(i,3,"cos")==0){
                i+=3; int exp=1; if(i<r && s[i]=='^'){ i++; int e=0; bool ok=false; while(i<r && isdigitc(s[i])){ ok=true; e=e*10+(s[i]-'0'); i++; } if(ok) exp=e; }
                if(i<r && s[i]=='x') i++; // consume the trailing x
                d += exp;
            }else if(s[i]=='x'){
                i++; int exp=1; if(i<r && s[i]=='^'){ i++; int e=0; bool ok=false; while(i<r && isdigitc(s[i])){ ok=true; e=e*10+(s[i]-'0'); i++; } if(ok) exp=e; }
                b += exp;
            }else{
                // skip unexpected character (shouldn't happen in valid input)
                i++;
            }
        }
        return Term(a,b,c,d);
    }

    Term get_term(int l, int r){ return parse_term_range(l,r); }

    // Helper to parse a polynomial segment without +/- separators: it's product of factors? For our input, between +/- we have multiplication concatenation; but they may include * explicitly. We'll implement full expression parser with +,-,*,/ and parentheses returning Frac.

    // Expression parsing using recursive descent. We treat lowest precedence +-, then */ , then unary +/- and factor.

    // Frac parse();

    Frac parse_expr(int l, int r){ // parse s[l:r)
        // Implement using tokenization with indices
        // For simplicity, create a local Parser over substring by using recursion over scan splitting by +,- at top level.
        // We'll implement generic functions that operate on substrings.
        return parse_sum(l,r);
    }

    int find_top_level(const string &str, int l, int r, char target){
        int bal=0;
        for(int i=l;i<r;i++){
            char c=str[i];
            if(c=='(') bal++;
            else if(c==')') bal--;
            else if(c==target && bal==0) return i;
        }
        return -1;
    }

    // split by + or - at top level, but need to keep signs; we'll left-to-right evaluate.
    Frac parse_sum(int l, int r){
        // Process terms separated by + or - at top level
        int i=l; Frac acc; bool acc_set=false; int last=i; int bal=0; char pending_op='+';
        while(i<r){
            char c=s[i];
            if(c=='(') bal++;
            else if(c==')') bal--;
            if((c=='+'||c=='-') && bal==0 && i>l){
                // segment [last,i)
                Frac seg = parse_prod(last,i);
                if(!acc_set){ acc = seg; acc_set=true; }
                else{
                    if(pending_op=='+') acc = acc + seg; else acc = acc - seg;
                }
                pending_op = c;
                i++; last=i; continue;
            }
            i++;
        }
        // tail
        if(last<r){
            Frac seg = parse_prod(last,r);
            if(!acc_set){ acc=seg; acc_set=true; }
            else{
                if(pending_op=='+') acc = acc + seg; else acc = acc - seg;
            }
        }else{
            if(!acc_set) acc = Frac(0);
        }
        return acc;
    }

    Frac parse_prod(int l, int r){
        int i=l; int bal=0; int last=l; Frac acc; bool acc_set=false; char pending_op='*';
        while(i<r){
            char c=s[i];
            if(c=='(') bal++;
            else if(c==')') bal--;
            if((c=='*' || c=='/') && bal==0){
                Frac seg = parse_factor(last,i);
                if(!acc_set){ acc=seg; acc_set=true; }
                else{ if(pending_op=='*') acc = acc * seg; else acc = acc / seg; }
                pending_op=c; i++; last=i; continue;
            }
            i++;
        }
        Frac seg = parse_factor(last,r);
        if(!acc_set) acc=seg; else { if(pending_op=='*') acc = acc * seg; else acc = acc / seg; }
        return acc;
    }

    Frac parse_factor(int l, int r){
        // strip surrounding parentheses
        while(l<r && s[l]==' ') l++; while(l<r && s[r-1]==' ') r--;
        if(l<r && s[l]=='('){
            int bal=0; bool ok=false; for(int i=l;i<r;i++){ if(s[i]=='(') bal++; else if(s[i]==')'){ bal--; if(bal==0){ if(i==r-1) ok=true; break; } } }
            if(ok){ return parse_sum(l+1,r-1); }
        }
        // unary +/-
        if(l<r && (s[l]=='+'||s[l]=='-')){
            char sign = s[l]; Frac f = parse_factor(l+1,r);
            if(sign=='-'){
                Frac z(0); return z - f; 
            }else return f;
        }
        // Otherwise, it's a term without +/- or */ at top level. It could be a pure integer like 123, or - already handled.
        // We must parse a Term by scanning tokens.
        Term t = get_term(l,r);
        return Frac::fromTerm(t);
    }

    Frac parse(){ return parse_sum(0,n); }
};

static void print_frac_two_lines(const Frac &f){
    print_frac(f);
}

int main(){
    ios::sync_with_stdio(false); cin.tie(nullptr);
    string expr; if(!getline(cin, expr)) return 0; Parser P(expr); Frac f = P.parse(); Frac df = f.derivate();
    // First line: fraction of f; second line: derivative fraction
    // Need to respect the special cases in print_frac: already prints newline.
    print_frac_two_lines(f);
    print_frac_two_lines(df);
    return 0;
}
