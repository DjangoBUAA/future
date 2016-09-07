#include "route.h"
#include "lib_record.h"
#include <map>
#include <queue>
#include <stack>
#include <vector>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/timeb.h>
using namespace std;

const int N=600;//最大节点数
const int INF=100000;//一个很大的数，代表无限
const int TIMELIMIT=9500;//迭代最长时间

//蚂蚁算法参数
const double ALPHA=2.0;//启发因子，信息素重要程度
const double BETA=0.5; //期望因子，节点花费重要程度
const double ROU=0.8;  //信息素挥发因子(这里表示残余量)

const int ANT_COUNT=10;//蚂蚁数量

const double DBQ=1;//总的信息素

class Demand{
	
public:
   	int n,nSize;
	int inSet[50];
	int src,dst;
        bool has[N];//是否是必经点
	Demand(){
		n=0;
		nSize=0;
		fill_n(has,N,false);
	}
	void read(char *demand){
		src = atoi(strtok(demand,","));
		dst = atoi(strtok(NULL,","));
		char* inc = strtok(NULL,",");
		inc = strtok(inc,"|");
		int ss = atoi(inc);
		add(ss);
		set(ss);		
		while((inc = strtok(NULL,"|"))!=NULL){
			ss = atoi(inc);
			add(ss);
			set(ss);
		}
	}
	int count() const{
		return n;
	}
	int size() const{
		return nSize;
	}
	
	int* begin(){
		return inSet;
	}
	int* end(){
		return inSet+nSize;
	}
	void add(int i){
		inSet[nSize++]=i;
	}
	void set(int i){
		if(!has[i]){
			has[i]=true;
			n++;
		}
	}
    void clear(int i){
        if(has[i]){
            has[i]=false;
            n--;
        }
    }
	void reset(){
		for(int i=0;i<nSize;i++){
			has[inSet[i]]=true;
		}
	}
	void print(){
		cout<<"Demand:";
		for(int i=0;i<nSize;i++){
			cout<<inSet[i]<<" ";
		}cout<<endl;
	}
};

struct Node{
	int edge;
	int cost;
	double prob;
	Node(){}
	Node(int e,int c,double p){
		edge=e;
		cost=c;
		prob=p;
	}
};

class Graph{
public:
	Graph(void){max=0;}
	~Graph(void){}
public:
	int max;
	map<int,Node>head[N];
public:
	void read(char** topo,int size,Demand dm){
		int id,src,dst,cst;
		for(int i = 0; i < size; i++){
			id = atoi(strtok(topo[i],","));
			src = atoi(strtok(NULL,","));
			dst = atoi(strtok(NULL,","));
			cst = atoi(strtok(NULL,","));
			auto &h=head[src];
			if(h.find(dst)!=h.end()){
				if(cst>h[dst].cost)
					continue;
				h[dst].edge=id;
				h[dst].cost=cst;
			}else{
				if(src>max)max=src;
				if(dst>max)max=dst;
				Node n(id,cst,dm.has[src]&&dm.has[dst]?1.0:dm.has[dst]?0.8:dm.has[src]?0.6:0.1);
				//Node n(id,cst,1.0);
				head[src][dst]=n;				
			}
		}
	}
	void print(){
		for(int i=0;i<N;i++){
			if(head[i].empty())
				continue;
			cout<<i<<": ";
			for(auto &v:head[i]){
				cout<<v.first<<"("<<v.second.edge<<","<<v.second.cost<<") ";
			}
			cout<<endl;
		}
	}
};

struct heapnode{
	int v,cost;
	heapnode(int d,int c){v=d,cost=c;}
	bool operator<(const heapnode&a)const{
		return cost>a.cost;
	}
};

int dijkstra(Graph* g,vector<int>& pt,bool tabu[],int src,int dst){
	int n=g->max+1;
	int path[n];
	int cost[n];
	bool visit[n];
	fill_n(path,n,-1);
	fill_n(cost,n,INF);
	fill_n(visit,n,false);
	int save=src;
	priority_queue<heapnode>q;
	q.push(heapnode(src,0));
	while(!q.empty()){
		heapnode min=q.top();q.pop();
		int& u=min.v;
		if(visit[u])
			continue;
		//termination: u is dst;
		if(u==dst){
			save=u;
			break;
		}
		visit[u]=true;
		for(auto &e:g->head[u]){// for each u's child
			const int& v=e.first;
			if(tabu[v])continue;
			int cst=min.cost+e.second.cost;
			if(cost[v]>cst){
				cost[v]=cst;
				path[v]=u;
				q.push(heapnode(v,cst));
			}
		}
	}
	if(-1==path[save]){// no path
		return -1;
	}else{		
		int u=save;
		stack<int>s;
		while(u!=src){
			s.push(u);
			u=path[u];
		}
		while(!s.empty()){
			pt.push_back(s.top());s.pop();
		}
		return cost[save];
	}
}

double rnd(double x){
	return x*rand()/(RAND_MAX+1.0);
}

class Ant{
private:
	Graph *graph;
	Demand *demand;
	bool stop;//搜索是否结束
	int current;//当前所在节点
	bool visited[N];//是否已访问
public:
	Ant(void){
		graph=NULL;
		demand=NULL;
	}
	~Ant(void){}
public:
	int mustpass;//包含的必经节点
	int cost;//蚂蚁走过路程的耗费
	vector<int> path;//蚂蚁走的路径
	
public:
	void SetMap(Graph &g){
		graph=&g;
	}
	void SetDemand(Demand &dm){
		demand=&dm;
	}
	void Init(){
		if(!demand){
			cout<<"Demand Not Set!"<<endl;
			exit(-1);
		}
		cost=0;
		stop=false;
		mustpass=0;
		path.clear();
		current = demand->src;			
		fill_n(visited,N,false);
		visited[current]=true;
		path.push_back(current);
	}
	
	int Next(){
		if(!graph){
			cout<<"Graph Not Set!"<<endl;
			exit(-1);
		}
		int selected=-1;
		int cnt=0;
		double total=0;//信息素总和
		int allow[8];//蚂蚁当前可走路径
		double prob[8];//蚂蚁当前可走路径的概率
		fill_n(prob,8,0);
		fill_n(allow,8,-1);
		for(auto &v:graph->head[current]){
			allow[cnt]=v.first;
			prob[cnt]=pow(v.second.prob,ALPHA)*pow(1.0/v.second.cost,BETA);
			total+=prob[cnt++];
		}
		if(total>0){//轮盘赌选择
			double tmp=rnd(total);
			for(int i=0;i<cnt;i++){
				tmp-=prob[i];
				if(tmp<0&&!visited[allow[i]]){
					selected=allow[i];
					break;
				}
			}
		}
		if(selected==-1){//防止信息素过小产生误差
			for(int i=0;i<8;i++){
				if(!visited[allow[i]]){
					if (demand->has[allow[i]]) {
						selected=allow[i];
						break;
					}
					else
						selected=allow[i];
				}
			}
		}
		return selected;
	}
	
	void Move(){
		if(!graph){
			stop=true;
			cout<<"Graph not Set!"<<endl;
			exit(-1);
		}
		if(!demand){
			stop=true;
			cout<<"Demand Not Set!"<<endl;
			exit(-1);
		}
		int next = Next();
		if(next==-1){
			stop=true;
			return;
		}
		if(next==demand->dst) {
			cost+=graph->head[current][next].cost;
			current = next;
			path.push_back(current);		
			visited[current]=true;
			stop=true;
			return;
		}
		cost+=graph->head[current][next].cost;
		current = next;
		path.push_back(current);		
		visited[current]=true;
		if(demand->has[current]){
			mustpass++;
			if(mustpass==demand->count()){
				stop=true;
				int cst=dijkstra(graph,path,visited,path.back(),demand->dst);
				if(cst!=-1){cost+=cst;}
				else{
					cout<<"no path to dest!"<<endl;
				}
			}
		}
	}
	
	void Search(){
		Init();
		while(!stop){
			Move();
		};
	}
	
	int Success(){
		bool dest=path.back()==demand->dst;
		bool must=mustpass==demand->count();
		return dest&&must?3:dest?2:must?1:0;
	}
	
	void Print(){
		if(path.empty())return;
		for(auto &v:path){
			string c="";
			if(demand->has[v])c="*";
			if(v!=path.back())
			cout<<v<<c<<"->";
		}cout<<path.back()<<endl;
	}
	
};

class Problem{
private:
	Graph *graph;
	Demand *demand;
	int cost;//某蚂蚁所求路径权值
	int count;//蚂蚁所求路径权值连续相同次数
public:
	Problem(void){}
	~Problem(void){}
public:
	Ant best;
	Ant ants[ANT_COUNT];
public:
	void Init(Graph& g,Demand& dm){
		best.cost=INF;
		for(int i=0;i<ANT_COUNT;i++){
			count=0;
			cost=INF;
			graph=&g;
			demand=&dm;
			ants[i].SetMap(g);
			ants[i].SetDemand(dm);
		}
	}
	
	void UpdateTrial(){//更新环境信息素
		//信息素挥发
		for(unsigned int i=0;i<N;i++){
			auto &head=graph->head[i];
			if(head.empty())continue;
			for(auto &e:head){
				e.second.prob*=ROU;
			}
		}
		
		//信息素更新
		for(int i=0;i<ANT_COUNT;i++){
			Ant& ant=ants[i];
			if(ant.Success()==0) continue;
			for(unsigned int j=1;j<ant.path.size();j++){
				int &src=ant.path[j-1];
				int &dst=ant.path[j];
				if (ant.Success()==3) 			
					graph->head[src][dst].prob += DBQ/ant.cost;
				else if (ant.Success()==2) 
					graph->head[src][dst].prob += ant.mustpass/(ant.cost*demand->size());
				else{
					if(demand->has[src]||demand->has[dst])
						graph->head[src][dst].prob += ant.mustpass/demand->size();
				}
									
			}
		}
	}
	
	bool canStop(){//如果蚂蚁0连续20次权值相同,则认为算法已收敛
		if(cost==ants[demand->size()].cost){
			count++;
		}else{
			count=0;
			cost=ants[demand->size()].cost;
		}
		if(count>20)return true;
		else return false;
	}
	
	void Search(){
		//迭代至时间耗尽
		clock_t startTime=clock();
		while((clock()-startTime)/1000<TIMELIMIT){
			//每只蚂蚁搜索一遍
			for(int j=0;j<ANT_COUNT;j++){
				ants[j].Search();
			}
			//保存最佳结果
			for(int j=demand->size();j<ANT_COUNT;j++){
				//ants[j].Print();
				if(ants[j].Success()==3&&ants[j].cost<best.cost){
					best=ants[j];
				}
			}
			UpdateTrial();
			if(canStop())break;
		}
	}
	
	void Output(){
		for(unsigned int i=1;i<best.path.size();i++){
			int &src=best.path[i-1];
			int &dst=best.path[i];
			record_result(graph->head[src][dst].edge);
		}
	}
	
	void Verify(){
		cout<<"begin verify..."<<endl;
		bool wrong=false;
		int cost=0,cnt=0;
		int visit[N];
		fill_n(visit,N,0);
		if(best.path.empty()){
			cout<<"No path found!"<<endl;
			return;
		}
		if(best.path.back()!=demand->dst){
			cout<<"last node wrong"<<endl<<"current path is:";
			for(auto n:best.path){
				string c="";
				if(demand->has[n])c="*";
				if(n!=best.path.back())
					cout<<n<<c<<"->";
			}cout<<best.path.back()<<endl;
			wrong=true;
		}
		for(unsigned int i=1;i<best.path.size();i++){
			int &src=best.path[i-1];
			int &dst=best.path[i];
			auto &head=graph->head[src];
			if(head.find(dst)==head.end()){
				cout<<"edge not exist:"<<src<<"->"<<dst<<endl;
				wrong=true;
			}
			cost+=head[dst].cost;
			if(visit[src]){
				cout<<"repass node:"<<src<<endl;
				wrong=true;
			}
			visit[src]=1;
			if(demand->has[src])
				cnt++;
		}
		if(demand->has[best.path.back()])cnt++;
		if(demand->count()!=cnt){
			cout<<"missing must pass node"<<endl;
			cout<<"total:"<<demand->count()<<endl;
			cout<<"unpass:"<<endl;
			for(int i=0;i<N;i++){
				if(!visit[i]&&demand->has[i])cout<<i<<" ";
			}
			cout<<endl;
			wrong=true;
		}
		if(wrong){
			cout<<"verify failed!"<<endl;
			return;
		}
		cout<<"best cost:"<<cost<<endl<<"shortest path:"<<endl;
		for(unsigned int i=1;i<best.path.size();i++){
			int &src=best.path[i-1];
			int &dst=best.path[i];
			string c="";
			if(demand->has[src]){c="*";}
			cout<<src<<c<<"("<<graph->head[src][dst].cost<<")->";
		}
		cout<<best.path.back()<<endl<<"verify succed!"<<endl;
	}

};


//你要完成的功能总入口
void search_route(char *topo[5000], int num, char *demand)
{
	Demand dm;
	dm.read(demand);
	Graph g;	;
	g.read(topo,num,dm);
	Problem m;
	m.Init(g,dm);
	m.Search();
	m.Verify(); 
	m.Output();
}
