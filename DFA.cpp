#include <iostream>
#include <string>
#include <stdio.h>
#include <stack>
#include <string.h>
#include <stdexcept>
#include <stdlib.h>
#include <set>

using namespace std;

const int Match = 256;
const int Split = 257;//表示epsilon分支

struct Paren{//括号结构体
    int natom;
    int nalt;
};

string re2post(string re){//正则表达式转后缀表达式
    Paren paren;//括号
    stack<struct Paren>parenStk;
    string postExpr="";
    int i, len=re.length();
    int nalt=0, natom=0;
    const string invalidRegExp = "Illegal regular expression";
    for(i=0; i<len; i++){
        if(isspace(re[i])) continue;
        if(isalpha(re[i])){
            if(natom>1){
                natom--;
                postExpr = postExpr + '.';
            }
            natom++;
            postExpr = postExpr + re[i];
        }
        else if(re[i]=='('){
            if(natom>1){
            	natom--;
                postExpr = postExpr + '.';
            }
            paren.natom = natom;
            paren.nalt = nalt;
            parenStk.push(paren);
            nalt = 0;
            natom = 0;
        }
        else if(re[i]==')'){
            if(natom==0 || parenStk.empty())
                throw runtime_error(invalidRegExp+":Brackets do not match ");
            while(--natom>0){//比如((a|b)(c|d))模式，当上一次匹配完倒数第二个右括号后，natom为2，需要添加'.'
                postExpr = postExpr + '.';
            }
            while(nalt-->0){
                postExpr = postExpr + '|';
            }
            paren=parenStk.top();
            parenStk.pop();
            natom = paren.natom;
            nalt = paren.nalt;
            natom++;
        }
        else if(re[i]=='*'){
            if(natom==0)
                throw runtime_error(invalidRegExp+":Appear ahead of time '*'");
            postExpr = postExpr + re[i];
        }
        else if(re[i]=='|'){
            if(natom==0) throw runtime_error(invalidRegExp+":Appear ahead of time '|'");
            while(--natom>0){
                postExpr = postExpr + '.';
            }
            nalt++;
        }
        else
            throw runtime_error(invalidRegExp);
    }
    if(!parenStk.empty())
        throw runtime_error(invalidRegExp+":Brackets do not match");
    while(--natom>0){
        postExpr = postExpr + '.';
    }
    while(nalt-->0){
        postExpr = postExpr + '|';
    }
    return postExpr;
}

class NFA;

/*
* c<256表示edge权重为c；
* c=256表示终结状态，匹配成功
* c=257表示分支（split）
*/
class State{
    friend class NFA;
    friend void nfa2graph(State* head, const string& re);
public:
    State(int c=256, State* out=NULL, State* out1=NULL){
        this->c = c;
        this->out = out;
        this->out1 = out1;
        this->id = 0;
    }
    void setId(int id){
        this->id = id;
    }

private:
    int c;
    int id;//状态的编号
    State* out;//从本状态出去的状态集合的头指针
    State* out1;//两个分支的情况
};

struct subset{//子集构造
	set<int > I[257];
	int sflag=0;
	int state=0;//0：不可接受状态		1：可接受状态
	int statenum;
	int id;
}s[100];

struct minDfa{
	set<int > subset;
	
}newstate[100];

set<int> S[100];//新的状态集合
int flag[100];

class NFA{
public:
    NFA(){
        head = NULL;
        tail = NULL;
    }
    NFA(const int& c){
        tail = new State(Match, NULL, NULL);
        head = new State(c, tail, NULL);
    }
    void doCat(NFA& nfa){
        tail->out = nfa.head;
        tail->c = Split;
        tail = nfa.tail;
        nfa.head = NULL;
        nfa.tail = NULL;
    }
    void doUnion(NFA& nfa){
        State* newHead = new State(Split, head, nfa.head);
        State* newTail = new State(Match, NULL, NULL);
        tail->c = Split;
        tail->out = newTail;
        nfa.tail->c = Split;
        nfa.tail->out = newTail;
        tail = newTail;
        head = newHead;
        nfa.head = NULL;
        nfa.tail = NULL;
    }
    void doStar(){
        State* newTail = new State(Match, NULL, NULL);
        State* newHead = new State(Split, head, newTail);
        tail->c = Split;
        tail->out = newTail;
        tail->out1 = head;
        tail = newTail;
        head = newHead;
    }
    void doSubset(State *p,int id)
    {
    	//cout<<p->id<<endl;
    	if(p!=NULL)
    	{
    		S[id].insert(p->id);
    		//cout<<S[id].size()<<endl;
    		if(p->c==Split)
    		{
    			S[id].insert(p->out->id);
    			if(p->out1!=NULL)
    			{
    				S[id].insert(p->out1->id);
    				doSubset(p->out1,id);
    			}
		    	doSubset(p->out,id);
    		}
    	}
    	//printf("S[%d].size=%d \n",id,(int)S[id].size());
    }
    void staClosure(State *p)
    {
    	if(p!=NULL)
    	{
	    	if(flag[p->id]==0)
	    	{
	    		flag[p->id]=1;
	    		doSubset(p,p->id);    	
	    	}
	    	staClosure(p->out);
	    	if(p->out1!=NULL&&flag[p->out1->id]==0)
	    		staClosure(p->out1);	    	
	    }
    }
    void Dfa(State *p,int id,int i){
    	if(p!=NULL)
    	{
	    	if(flag[p->id]==0)
	    	{
	    		flag[p->id]=1;
	    		if(p->id==id){
	    			if(p->c<Match)
	    				s[i].I[p->c].insert(S[p->out->id].begin(),S[p->out->id].end());
	    			else
	    				s[i].state=1;
	    		}
	    	}
	    	Dfa(p->out,id,i);
	    	if(p->out1!=NULL&&flag[p->out1->id]==0)
	    		Dfa(p->out1,id,i);	    	
	    }
    }
    int init_Dfa(State *p){
    	s[1].I[0]=S[1];//初始化最初态
    	s[0].statenum=1;
    	//cout<<s[1].I[0].size()<<endl;
    	int a;
    	while(1)
    	{
    		int i=1;
    		while(s[i].I[0].size()!=0 && s[i].sflag==1)
    			i++;
    		//cout<<i<<endl;
    		if(s[i].I[0].size()==0)
    		{   		
    			a=i;
    			break;
    		}
   	        for(auto j=s[i].I[0].begin();j!=s[i].I[0].end();j++)
	        	if(S[*j].size()==1)
	        	{
	        		//cout<<*j<<endl;
	        		memset(flag,0,sizeof(flag));
	        		Dfa(p,*j,i); 
	        		//cout<<s[i].I[98].size()<<endl;		
	        	}
	        //cout<<s[i].I[97].size()<<endl;

	        for(int j=97;j<=122;j++)
	        {
	        	if(s[i].I[j].size()==0)
	        		continue;
		        int k=1;
		    	
		        while(k<=s[0].statenum)
		        {
		        	if(s[k].I[0]==s[i].I[j])
		        		break;
		        	k++;
		        }		
		        if(k>s[0].statenum)
		        {
		        	s[0].statenum++;
		        	s[k].I[0]=s[i].I[j];
		        }
		    }
		    s[i].sflag=1;
    	}
    	return a;
    }
    int get_loc(set<int > a)
    {
    	int i=1;
    	for( i=1;i<=s[0].statenum;i++)
    		if(a==s[i].I[0])
    			return i;
    	return 0;
    }
    int find_Next(minDfa a[],int id,int c)
    {
    	int loc=get_loc(s[id].I[c]);
    	if(loc==0)
    		return 0;
    	int i;
    	for(i=1;a[i].subset.size()!=0;i++)
    	{
    		for(auto n=a[i].subset.begin();n!=a[i].subset.end();n++)
    		if(*n==loc)
    			return i;
    	}
    	return -1;
    }
    bool compare(minDfa a[],int id1,int id2,int c)
    {
    	int p1,p2;
    	int i=get_loc(s[id1].I[c]);
    	int j=get_loc(s[id2].I[c]);
    	int k=0;
    	//cout<<i<<" "<<j<<endl;
    	
    	while(a[k].subset.size()!=0)
    	{
    		for(auto n=a[k].subset.begin();n!=a[k].subset.end();n++)
    		{
    			if(*n==i)
    				p1=k;
    			if(*n==j)
    				p2=k;
			}
    		k++;
    	}
    	if(p1==p2)
    		return true;
    	else
    		return false;
    }
    void min_Dfa(int n){
        //int j=1;
        newstate[0].subset.insert(0);

        for(int i=1;i<n;i++)
        {
        	if(s[i].state==0)
        		newstate[2].subset.insert(i);
        	else
        		newstate[1].subset.insert(i);
        }
        int num;
        if(newstate[2].subset.size()!=0)
        	num=2;
        else
        	num=1;
        /*if(compare(newstate,1,2,99))
        	cout<<"1\n";
        else
        	cout<<"0\n";*/
        //int min_part=0;
    	for(int i=1;newstate[i].subset.size()!=0;i++)
    	{	
    		int min_part=0;
    		while(1)//如果该分区出现分区操作，则对此分区进行再分区直到该分区目前不可分
    		{
    			int min_flag=0;//默认操作
    			for(int k=97;k<=122;k++)
	    		{
	    			auto t=newstate[i].subset.begin();
	    			auto j=t;
	    			if(newstate[i].subset.size()==1)
	    			{
	    				//min_part=1;
	    				break;
	    			}
	    			while(j!=newstate[i].subset.end())
	    			{
	    				j++;
	    				if(j==newstate[i].subset.end())
	    					break;
		        		/*
		        		printf("%dmin_Dfa%d:\n",*j,i);
				        for(int b=1;newstate[b].subset.size()!=0;b++)
				        {
				        	printf("%d:\t",b);
				        	for(auto w=newstate[b].subset.begin();w!=newstate[b].subset.end();w++)
				        		printf("%d ",*w);
				        	cout<<"\n";
				       	}
				       	*/
	    				//cout<<*j<<endl;
	    				if(compare(newstate,*t,*j,k))
	    				{
	    					//min_flag=1;
	    					continue;
	    				}
	    				min_flag=1;
	    				//printf("%d %d not match\n",*t,*j);
	    				min_part=1;//有分区操作
	    				newstate[num+1].subset.insert(*j);
    					newstate[i].subset.erase(*j);
    					j--;
	    			}
    		    	//cout<<"\n";
    		    }
    		    if(min_flag==0) 
    		    {
    		    	if(min_part==1)
						num++;				
    		    	break;
    		    }
    		}
    		if(min_part==1)
    			i=0;
	    }
       	
    }
    void nfa2graph(const string& re){
        char myfile[100];
        printf("please input a filename to save NFA-graph:\n");
        scanf("%s", myfile);
        printf("\"%s.dot\",\n", myfile);
        printf("\"%s.dot.pdf\".\n", myfile);
        int i=0;
        while(myfile[i]!='\0')
            i++;
        myfile[i] = '.';
        myfile[i+1] = 'd';
        myfile[i+2] = 'o';
        myfile[i+3] = 't';
        myfile[i+4] = '\0';
        //cout<<myfile<<endl;
        FILE *file = fopen(myfile, "w");

        fputs("digraph {\n", file);
        fputs("\t\"", file);
        int len=re.length();
        for(i=0; i<len; i++){
            fprintf(file, "%c", re[i]);
        }

        fputs("\" [shape = plaintext]\n", file);
        fputs("\trankdir = LR\n", file);
        fputs("\t\"\" [shape = point]\n", file);
        fputs("\t\"\" -> 1 [label = Start]\n\n", file);

        int id = 1;

        char circle[2000];
        memset(circle, 0, sizeof(circle));
        State* p;
        stack<State*> staStk;

        head->setId(id++);
        staStk.push(head);

        while(!staStk.empty()){
            p = staStk.top();
            staStk.pop();
            char flag = 1;
            cout << "p->c=" << p->c << endl;
            if(p->c < Match){
                cout << "p->out->id=" << p->out->id << endl;
                if(p->out->id==0){
                    p->out->id = id++;
                    cout << "id=" << id << endl;
                }
                else
                    flag = 0;
                fprintf(file, "\t%d -> %d [label = \"%c\"]\n", p->id, (p->out)->id, p->c);
                State *what = p->out;
                if(flag) //push(*what);
                    staStk.push(what);
            } 
            else if(p->c == Match)
                circle[p->id] = 1;
            else{     //对应Split的情形
                if(p->out->id==0)
                    p->out->id = id++;
                else
                    flag = 0;
                fprintf(file, "\t%d -> %d [label = <ε>]\n", p->id, p->out->id);
                State *what = p->out;
                if(flag) staStk.push(what);

                if(p->out1!=NULL){
                    flag = 1;

                    if(p->out1->id==0)
                        p->out1->id = id++;
                    else
                        flag = 0;
                    fprintf(file, "\t%d -> %d [label = <ε>]\n", p->id, p->out1->id);
                    what = p->out1;
                    if(flag) staStk.push(what);
                }
            }
        }

        for(i=1; i<id; i++){
            fprintf(file, "\t%d [shape = circle", i);
            if(circle[i])
                fputs(", peripheries = 2", file);
            fprintf(file, "]\n");
        }
        State *q;	
        q=head;
        staClosure(q);
        /*
        for(i=1;i<id;i++)
        	cout<<flag[i]<<" ";
        cout<<endl;
        */
   		for(int j=1;j<id;j++)
   		{
   			printf("S[%d]=",j);
	        for(auto i=S[j].begin();i!=S[j].end();i++)
	        	cout<<*i<<" ";
	        cout<<endl;
	    }
	    int k=init_Dfa(q);
	    printf("state:\n");
		for(i=1;i<k;i++)
		{
			for(auto j=s[i].I[0].begin();j!=s[i].I[0].end();j++)
	        	cout<<*j<<" ";
	        printf("(%d)",s[i].state);
	        for(int j=97;j<=122;j++)
	        	if(s[i].I[j].size()!=0)
	        	{
	        		printf("\tI%c: ",j);
	        		for(auto t=s[i].I[j].begin();t!=s[i].I[j].end();t++)
	        			cout<<*t<<" ";
	        	}
	        cout<<endl;
		}
		cout<<"id="<<id<<endl;
		cout<<"state_num="<<k-1<<endl;
        for(i=1;i<k;i++){
        	s[i].id=i+id-1;
        	for(int j=97;j<=122;j++)
	        	if(s[i].I[j].size()!=0)
	 			{
	 				int loc=get_loc(s[i].I[j]);
	 				//cout<<"loc="<<loc<<endl;
	        		fprintf(file, "\t%d -> %d [label = <%c>]\n", s[i].id,loc+id-1,j);
	        	}
        }
        for(i=id; i<id+k-1; i++){
            fprintf(file, "\t%d [shape = circle", i);
            if(s[i+1-id].state==1)
                fputs(", peripheries = 2", file);
            fprintf(file, "]\n");
        }
        min_Dfa(k);
        cout<<"k="<<k<<endl;
        printf("min_Dfa:\n");
        for(int j=1;newstate[j].subset.size()!=0;j++)
        {
        	printf("%d:\t",j);
        	for(auto w=newstate[j].subset.begin();w!=newstate[j].subset.end();w++)
        		printf("%d ",*w);
        	cout<<"\n";
        }
        id=id+k-2;//Min_Dfa初始id-1
        for(int j=1;newstate[j].subset.size()!=0;j++)
        {
        	auto w=newstate[j].subset.begin();
        	printf("newstate[%d].begin=%d\n",j,*w);
        	for(int c=97;c<=122;c++)
        	{
        		int l=find_Next(newstate,*w,c);

        		if(l==0)
        			continue;
        		printf("%d.I%c=%d\n",*w,c,l);
        		fprintf(file, "\t%d -> %d [label = <%c>]\n",id+j,id+l,c);
        	}
        }
        for(i=1;newstate[i].subset.size()!=0; i++){
            fprintf(file, "\t%d [shape = circle", i+id);
            auto w=newstate[i].subset.begin();
            if(s[*w].state==1)
                fputs(", peripheries = 2", file);
            fprintf(file, "]\n");
        }
        fputs("}", file);
        fclose(file);

        char cmd[108];
        sprintf(cmd, "dot %s -O -Tpdf", myfile);
        if(system(cmd)==0){
            printf("pdf succeed!\n");
            //printf("Linux用户可以使用evince file.pdf &命令打开~\n");
        }
        else
            printf("pdf failed..\n");
    }
private:
    State* head;
    State* tail;
};

NFA post2nfa(const string& postExpr){
    stack<NFA> nfaStk;
    NFA e1, e2, e;
    int i, len=postExpr.length();
    for(i=0; i<len; i++){
        switch(postExpr[i]){
        case '.':
            e2 = nfaStk.top();
            nfaStk.pop();
            e1 = nfaStk.top();
            nfaStk.pop();
            e1.doCat(e2);
            nfaStk.push(e1);
            break;
        case '|':
            e2 = nfaStk.top();
            nfaStk.pop();
            e1 = nfaStk.top();
            nfaStk.pop();
            e1.doUnion(e2);
            nfaStk.push(e1);
            break;
        case '*':
            e = nfaStk.top();
            nfaStk.pop();
            e.doStar();
            nfaStk.push(e);
            break;
        default://
            NFA alpha(postExpr[i]);
            nfaStk.push(alpha);
        }
    }
    e = nfaStk.top();
    nfaStk.pop();
    if(!nfaStk.empty())
        throw runtime_error("wrong");
    return e;
}

bool match(char c[100])
{
	int len=strlen(c);
	int id=1;
	NFA nfa;
	for(int i=0;i<len;i++)
	{
		int edge=(int)c[i];
		//printf("I%c\n",edge);
		if(s[id].I[edge].size()==0)
			return false;
		id=nfa.get_loc(s[id].I[edge]);
		//printf("next_id=%d\n",id); 
	}
	if(s[id].state==1)
		return true;
	else
		return false;
}
int main(){
    string re;
    cout << "input a regular exp:\n";
    cin >> re;
    string postExpr = re2post(re);
    cout << "postExpr is : " << postExpr << endl;
    NFA nfa = post2nfa(postExpr);
    nfa.nfa2graph(re);
    char c[100];
    while(1)
    {
	    printf("input strings :");
	    scanf("%s",c);
	    //printf("the strings :%s\n",c);
	    if(match(c))
	    	cout<<"match succeed\n";
	    else
	    	cout<<"match failed\n";
	    printf("y:continue\tn:end\n");
	    char op;
	    cin>>op;
	    if(op=='n')
	    	break;
	}
	cout << "Bye~\n";
    return 0;
}