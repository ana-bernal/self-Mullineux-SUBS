
# The following is a sequence of functions to define the function
# EBeta which takes a prime e and a self-Mullineux partitions and
# returns the BG-partition associated under the correspondence
# defined from the Mullineux symbol.

DiagramPartition:=function(mu)
# Takes a partition mu and returns the set of nodes that form the Young 
# diagram of mu.
local d,i,j;
if mu=[] then
	return [];
else
   d:=[];
   for i in [1..Length(mu)] do
     for j in [1..mu[i]] do
      Add(d,[i,j]);
     od;
   od;
   return Set(d);
fi;
end;

Rim:=function(mu)
# Takes a partition mu and returns the set of nodes (i,j) of the rim of mu
 local r,c;
 r:=[];
	 for c in DiagramPartition(mu) do
 		if not ( [c[1]+1,c[2]+1] in DiagramPartition(mu) ) then
 		Add(r,c);
 		fi;
 	 od;
return Set(r);
end;


OrgRim:=function(mu)
# Takes a partition mu and returns a list of the nodes of the rim of the diagram of mu, organized from "north-east" to "south-west" of the Young diagram.
 local r,i,j;
 r:=[];
 if mu=[] then
 	return [];
 else
 	for i in [1..Length(mu)] do
 		j:= mu[i];
 		while j > 0 do
 			if [i,j] in Rim(mu) then
 			Add(r,[i,j]);
 			fi;
 			j:= j-1;
 		od;
 	od;	
 fi;
return r;
end;



HookLength:=function(la,i,j)
# Takes a partition la and a node (i,j) in the Young diagram of la and returns the hook-length of the (i,j)-th hook
	local lap,l;

	lap:=ConjugatePartition(la);
	l:= Length(la);

	if i >= 1 and i <=l and j>=1 and j<=la[i] then
		return la[i]-j+lap[j]-i+1;
	else
		Print("the node (",i,",",j,") is not in the Young diagram of ",la,"\n");
	fi;

end;

PartitionDiag:=function(nodes)
# Takes a set of nodes forming a Young diagram and returns the associated partition.

	local col,n,b,mu,i,j;

	mu:=[];
	n:= Length(nodes);

	if nodes=[] then
		return [];
	else
		i:=1;
		col:=[];

	
			while i<=n do
				for j in [1..n] do

					if [i,j] in nodes then
						Add(col,j);
					fi;
				od;

				if col=[] then
					return mu;
				else
					Add(mu,Maximum(col));
				fi;

				col:=[];
				i:=i+1;
			
			od;

		return mu;
	fi;
end;

DiagBoxRim:=function(mu)
# Takes a self-conjugate partition mu an returns i the only diagonal where (i,i) is the only diagonal node in the rim of mu.
 local i;
 	for i in [1..Length(mu)] do
 		if [i,i] in Rim(mu) then
 		return i;
 		fi;
 	od;
 end;

PRim1:=function(e,mu)
# Set U of the p-rim* of mu.
	local n,res,rim,d,i,k,mil,r,l,m,x,b,compte,muprime,prim,j;

	rim:= OrgRim(mu);  #rim de mu, organisé
	prim:= [];        #nodes of the PRim for autoconjugate partitions.
	m:= DiagBoxRim(mu); #la boite [m,m] est la boite diagonale dans le rim de mu.
	d:=Position(rim,[m,m]); #sa position dans la liste rim
	
	if mu=[] then
		return [];

	elif Length(rim) <= e then
		return rim;  

	else		

		i:=1;          #premiere boite de chaque rim

		while i <= d do   #on commence par ajouter à prim les p-rim d'au dessus.
			compte:= e;



			j:=i;  #boite actuelle que j'ajoute au rim (parcour rim)


			while compte <> 0 do

				if j <= Length(rim) then
					Add(prim,rim[j]);
					compte:= compte - 1;
					j:=j+1;
			 
				else 
					# Add(prim,rim[j]);

					return prim;
				fi;

			od;
			

			
			k:=j-1;           #derniere boite de ce rim

			if j-1 = Length(rim) then    #dans ce cas, celui-ci est le dernier rim d'au dessus.


				return prim;

			elif j-1 >= d then


				return prim;
			
			else   # dans ce cas on peut encore commencer un p-rim d'au dessus.

				while rim[k][1] = rim[j-1][1] do
					k:= k + 1;
				od;

				i:= k;
				compte:= e;
			fi;
			

			
		od;
	fi;



	return prim;
	end;


PRim2:=function(l,e)
# Fix the middle segment

	local r,enlever,b,mil,x;


	r:= Length(l) mod e;

		if r = 0 then

			r := e;
		fi;

		mil:=l{[Length(l)-r+1..Length(l)]}; #rim du milieu
		x:= mil[1]; #premiere boite du rim du milieu
		enlever:=[]; #boites a enlever

		for b in mil do
			if b[2]<x[1] then
			Add(enlever,b);
			fi;

		od;

		l:=Set(l);

		for y in enlever do

			RemoveSet(l,y);


		od;

	return l;



end;



PRim3:=function(e,mu)
# The subset U of the p-rim*
	local rim;
	rim:= PRim1(e,mu);

	rim:=PRim2(rim,e);

	return rim;
end;


PRim4:=function(e,mu)
# The reflection of subset U of the p-rim*
	local rim,srim,j,i,m,b,d,a,k,l,orgsrim,compte,res;

	rim:=OrgRim(mu);
	srim:=Set(rim);
	m:= DiagBoxRim(mu); #la boite [m,m] est la boite diagonale dans le rim de mu.
	d:=Position(rim,[m,m]); #sa position dans la liste rim
	
	for b in rim do

		if (Position(rim,b) <= d) or b in PRim3(e,mu) then
			RemoveSet(srim,b);
		fi;
	od;

	orgsrim:=[];
	
	j:=Length(mu);
	while j>0 do
    	for i in [1..mu[j]] do
    		if [j,i] in srim then
    			Add(orgsrim,[j,i]);
    		fi;
    	od;
    	j:=j-1;
	od;

# orgsrim est la liste de boites du rim au dessous de ladiagonale, maintenant il faut choisir lesquelles de ces boites sont dans le e-rim.

res:=[];

a:=1; #premiere boite de chaque e-rim
compte:=e;

	if Length(orgsrim)<=e then
		return orgsrim;

	else
		while a<=Length(orgsrim) do

			k:=a; #boite actuelle que j'ajoute au resultat

				while compte <> 0 do

					if k <= Length(orgsrim) then
						Add(res,orgsrim[k]);
						compte:= compte-1;
						k:=k+1;
					else
						return res;
					fi;
				od;

			l:=k-1;           #derniere boite de ce rim

			if k-1 = Length(orgsrim) then    #dans ce cas, celui-ci est le dernier rim d'au dessus.


				return res;

			
			else   # dans ce cas on peut encore commencer un p-rim d'au dessous.

				while orgsrim[l][2] = orgsrim[k-1][2] do
					l:= l + 1;
					if l>Length(orgsrim) then
						return res;
					fi;
				od;

				a:= l;
				compte:= e;


			fi;
			


		od;
	fi;


	return res;
end;

PRim5:=function(e,mu)
# p-rim* for self-conjugate mu
	local l;

	l:=PRim3(e,mu);
	Append(l,PRim4(e,mu));

	return l;

end;


ERim:=function(e,mu)
#Takes an odd prime e and a self-conjugate partition mu and returns [mu^(1)*,e-rim*] where e-rim is the e-rim* of a self-conjugate partition and mu^(1)* is the partition obtained from mu after deleting the e-rim*.
	local diag,erim,b ;

	erim:=PRim5(e,mu);
	diag:=Set(DiagramPartition(mu));

	for b in erim do
		RemoveSet(diag,b);
	od;

	return [PartitionDiag(diag),erim];
end;

AutoSymb:=function(e,mu)
# takes a prime e and a self-conjugate partition mu and returns the first line of the p-BG-symbol (first line) for mu

	local muprime,symb;

	symb:=[];

	if mu=[] then
		return [];

	else

		muprime:=mu;

		while muprime <> [] do
			Add(symb,Length(ERim(e,muprime)[2]));
			muprime:=ERim(e,muprime)[1];

		od;
		return symb;
	fi;
end;

EBGsymb:=function(p,mu)
# Takes a prime p and a self-conjugate partition mu and returns the p-BG-symbol mu
	local i, symb;

	symb:=[];
	symb[1]:=AutoSymb(p,mu);
	symb[2]:=[];

	for i in AutoSymb(p,mu) do
		if EuclideanRemainder(i,2)=0 then
		Add(symb[2],i/2);
		else
		Add(symb[2],(i+1)/2);
		fi;
	od;	
	return symb;
end;

EBetaInverse:=function(e,la)
# Takes an odd prime e, and a e-BG-partition la and returns the e-self-Mullineux partition corresponding to la under the bijection defined by the bg-symbol.
	local n,m,i,l,j ;

	n:=Sum(la);
	m:=1;
	j:=1;
	l:=Length(la);

	if la<>ConjugatePartition(la) then
		return Print("E: this is not a BG-partition. \n");
	fi;

	while  la[m]>=m do
		m:=m+1;
	od;
	m:=m-1;

	while j<=m and HookLength(la,j,j) mod e <> 0 do
		j:=j+1;
	od;
	j:=j-1;

	if j<m then
		return Print("E: this is not a BG-partition. \n");
	fi;
	
	return PartitionMullineuxSymbol(e,EBGsymb(e,la));

end;

DurfeeNumber:=function(mu)
# takes a partition and returns its durfee number
	local d,i,l;
    d:=1;
    l:=Length(mu);

    if mu=[0] then
        return 0;
    else 
        while d <= l and d<=mu[d] do
        d:=d+1;
        od;
    fi;
    
    return d-1;

end;

EBGPartitions:=function(p,n)
# Takes an odd prime p and an integer n and returns the list of pBG-partitions of n
    local list,d,la,i,inlist;

    list:=[];

    for la in Partitions(n) do
        if la=ConjugatePartition(la) then

        d:=DurfeeNumber(la);
        i:=1;
        inlist:=true;

        while i <= d and inlist=true do 

            if HookLength(la,i,i) mod p = 0 then
                inlist:=false;
            else i:= i+1;
            fi;

        od;

        if inlist=true then
            Add(list,la);
        fi;
        fi;

    od;

    return list;
end;



EBetaSymbol:=function(e,symb)
# Takes a prime e and the Mullineux symbol symb (list of rows) of a e-self-Mullineux partition and returns the associated e-BG-partition.
	local k,i,n,s;


	if MullineuxMap(e,PartitionMullineuxSymbol(e,symb))=PartitionMullineuxSymbol(e,symb) then
		n:=Sum(symb[1]);
		k:=0;
		i:=1;


		while k=0 do
			if EBGsymb(e,EBGPartitions(e,n)[i])=symb then
				k:=1;
				s:=EBGPartitions(e,n)[i];
			else
				i:=i+1;
			fi;
		od;

		return  s;
	else
		return Print("This is not the symbol of a ",e,"-self-mullineux partition.","\n");
	fi;

end;


EBeta:=function(e,mu)
# Takes a prime e and a e-self-Mullineux mu and returns the e-BG-partition partition corresponding to mu under the bijection defined by the bg-symbol.
	local symb ;
	if MullineuxMap(e,mu)=mu then
		return EBetaSymbol(e,MullineuxSymbol(e,mu));
	else return Print(mu," is not a ",e,"-self-mullineux partition");
	fi;
end;

###############################################################################
#
# The following is a list of functions to test which blocks of the
# symmetric group have compatible completely admissible transversals.
# 
###############################################################################


# Takes an integer e<n and n and returns all partitions in the block
# of S_n corresponding to the core core.
BlockPartitionsCore:=function(e,n,core)
	local mu, res;
	res:=[];

	for mu in Partitions(n) do
		if ECore(e,mu)=core then
			Add(res,mu);
		fi;
	od;

	return res;
end;

# Same as BlockPartitionsCore, but with the weight w.
BlockPartitionsWeightCore:=function(e,w,core)
	local mu, res,n;
	res:=[];

	n:=Sum(core)+ e*w;
	for mu in Partitions(n) do
		if ECore(e,mu)=core then
			Add(res,mu);
		fi;
	od;

	return res;
end;

# Returns all e-regular partitions on a block with a given core
BlockPartitionsCoreERegulars:=function(e,n,core)
	local mu, res;
	res:=[];

	for mu in BlockPartitionsCore(e,n,core) do
		if IsERegular(e,mu) then
			Add(res,mu);
		fi;
	od;

	return res;
end;

# Same but with weight 
BlockPartitionsWeightCoreERegulars:=function(e,w,core)
	local mu, res;
	res:=[];
	

	for mu in BlockPartitionsWeightCore(e,w,core) do
		if IsERegular(e,mu) then
			Add(res,mu);
		fi;

	od;

	return res;
end;

# visualize list with sm-partitions marked with *
BlockPartitionsWeightCoreERegularsVisual:=function(e,w,core)
	local mu, res;
	res:=[];
	

	for mu in BlockPartitionsWeightCore(e,w,core) do
		if IsERegular(e,mu) then
			if mu=MullineuxMap(e,mu) then 
				Print("* ",mu,"\n");
			else 
				Print("  ",mu,"\n");
			fi;
		fi;

	od;
end;

# Self-Mullineux partitions in the e-block with weight
BlockPartitionsWeightCoreERegularsSM:=function(e,w,core)
	local mu, res;
	res:=[];

	if w mod 2 = 1 or core<>ConjugatePartition(core) then 
		res:=[];
	
	else 
		for mu in BlockPartitionsWeightCore(e,w,core) do
			if IsERegular(e,mu) then
				if mu=MullineuxMap(e,mu) then 
					Add(res,mu);
				fi;
			fi;

		od;
	fi;

	return res;
end;


# returns all e-regular partitions of integers less than n
# of e weight w
EWeightWPart:=function(e,w,n)
	local res,mu,i;
	res:=[];
	
	if w=0 then 
		Add(res,[]);
	fi;

	for i in [1..n] do
		for mu in ERegularPartitions(e,i) do
			if EWeight(e,mu) = w then
				Add(res,mu);
			fi;
		od;
	od;

	return res;
end;

# Returns the list of e-cores of rank up to m
ListECores:=function(e,m)
	return EWeightWPart(e,0,m);
end;

# Returns the list of self-conjugate e-cores of rank up to m
ListECoresSC:=function(e,m)
	local resu,ga;

	resu:=[];

	for ga in EWeightWPart(e,0,m) do 
		if ga=ConjugatePartition(ga) then
			Add(resu,ga);
		fi;
	od;

	return resu;
end;

#list of all the e-cores of partitions of n
ECoresList:=function(e,n)
	local mu,res,core;
	res:=[];

	for mu in Partitions(n) do
		core:=ECore(e,mu);

		if (core in res)=false then
			Add(res,core);
		fi;
	od;

	return res;
end;

#list of all partitions of n organised by blocks (corresponding to e-cores)
PartitionsByBlocks:=function(e,n)
	local core,mu;

	for core in ECoresList(e,n) do
		Print("core=",core,"..weight=",(n-Sum(core))/e,"\n");
		for mu in Partitions(n) do
			if ECore(e,mu)=core then
				Print("  ",mu,"\n");
			fi;
		od;
	od;
end; 

# Returns the list formed by partitions with e-core core or core'
# and e-weight w
SSet:=function(e,w,core)
	local list;

	if IsECore(e,core)=false then
		Print(core, " is not a ", e, " core. \n");
	else 
		if core=ConjugatePartition(core) then
			return BlockPartitionsWeightCore(e,w,core);
		else 
			list:=BlockPartitionsWeightCore(e,w,core);
		Append(list, BlockPartitionsWeightCore(e,w,ConjugatePartition(core)));
		return list;
		fi;
	fi;
end;

# Returns the list of e-regular partitions in SSet(e,w,core)
SSetReg:=function(e,w,core)
	local list, res, la;
	
	if IsECore(e,core)=false then
		Print(core, " is not a ", e, " core. \n");
	else 
		list:=SSet(e,w,core);
		res:=[];

		for la in list do 
			if IsERegular(e,la) then
				Add(res,la);
			fi;
		od;
		return res;
	fi;
end;

# Returns a list of all the possible admissible
# transversals for the e-block of weight w of the
# block corresponding to the core core.
AdmTransversals:=function(e,w,core)
	local res, halflist, la, paire, size, transv,NEWtransv,x,i,mu,newx;

	# (any) "half" of the p-regular partitions in the block
	# this was particularly chosen using the lex order.
	halflist:=[];
	for la in SSetReg(e,w,core) do 
		if la>MullineuxMap(e,la) then 
			Add(halflist,la);
		fi;
	od;
	size:=Length(halflist);

	# list of couples [la_1,la_2] such that any of the two
	# could be in a transversal, or just [la] if only one
	# can be.
	res:=[];
	for la in halflist do 
		paire:=[];
		if Dominates(MullineuxMap(e,la),la)=false then
			Add(paire,la);
		fi;
		if Dominates(la,MullineuxMap(e,la))=false then
			Add(paire,MullineuxMap(e,la));
		fi;
		Add(res,paire);
	od;
		
	if Length(res[1])=1 then
		transv:=[res[1]];
	else
		transv:=[[res[1][1]],[res[1][2]]];
	fi;

	i:=2;

	while Length(transv[1])<size do 
		NEWtransv:=[];
		
		for x in transv do 
			for mu in res[i] do
				newx:=Copy(x);
				Add(newx,mu);
				Add(NEWtransv,newx);
			od;
		od;

		transv:=NEWtransv;
		i:=i+1;
	od;

	return transv;
end;

# For testing if the above functions gives in fact
# all admissible transversals we have to look for an
# example where there exists at least two adm. tr.
# For this, the following function looks for a block
# where this happens.
# The test function will look for e-blocks
# where the rank of the e-blocks goes up to m

Test1AdmTransversals:=function(e,m)
	local listcores,w,core;

	listcores:=ListECores(e,m);

	for core in listcores do
		for w in [1..5] do 
			if Length(AdmTransversals(e,w,core))>1 then 
				Print("# of transv= ",Length(AdmTransversals(e,w,core)),", weight= ",w,", core= ",core,"\n");
			fi;
		od;
	od;
end;

# Exemple p=3
# Test1AdmTransversals gives two possible admissible transversals
# first number is how many admissible transversals are there

# gap> Test1AdmTransversals(3,10);
# 2, weight= 5, core= [  ]
# 2, weight= 5, core= [ 1 ]
# 2, weight= 4, core= [ 1, 1 ]
# 8, weight= 5, core= [ 1, 1 ]
# 2, weight= 4, core= [ 2 ]
# 8, weight= 5, core= [ 2 ]
# 4, weight= 4, core= [ 2, 1, 1 ]
# 8, weight= 5, core= [ 2, 1, 1 ]
# 2, weight= 4, core= [ 3, 1 ]
# 8, weight= 5, core= [ 3, 1 ]
# 2, weight= 4, core= [ 3, 1, 1 ]
# 4, weight= 5, core= [ 3, 1, 1 ]
# 4, weight= 4, core= [ 2, 2, 1, 1 ]
# 8, weight= 5, core= [ 2, 2, 1, 1 ]
# 4, weight= 4, core= [ 4, 2 ]
# 4, weight= 5, core= [ 4, 2 ]
# 2, weight= 4, core= [ 4, 2, 1, 1 ]
# 4, weight= 5, core= [ 4, 2, 1, 1 ]
# 2, weight= 1, core= [ 3, 2, 2, 1, 1 ]
# 2, weight= 2, core= [ 3, 2, 2, 1, 1 ]
# 8, weight= 3, core= [ 3, 2, 2, 1, 1 ]
# 8, weight= 4, core= [ 3, 2, 2, 1, 1 ]
# 32, weight= 5, core= [ 3, 2, 2, 1, 1 ]
# 2, weight= 1, core= [ 5, 3, 1 ]
# 2, weight= 2, core= [ 5, 3, 1 ]
# 4, weight= 3, core= [ 5, 3, 1 ]
# 4, weight= 4, core= [ 5, 3, 1 ]
# 4, weight= 5, core= [ 5, 3, 1 ]
# 2, weight= 1, core= [ 4, 2, 2, 1, 1 ]
# 2, weight= 2, core= [ 4, 2, 2, 1, 1 ]
# 8, weight= 3, core= [ 4, 2, 2, 1, 1 ]
# 8, weight= 4, core= [ 4, 2, 2, 1, 1 ]
# 16, weight= 5, core= [ 4, 2, 2, 1, 1 ]
# 2, weight= 1, core= [ 5, 3, 1, 1 ]
# 2, weight= 2, core= [ 5, 3, 1, 1 ]
# 4, weight= 3, core= [ 5, 3, 1, 1 ]
# 2, weight= 4, core= [ 5, 3, 1, 1 ]
# 4, weight= 5, core= [ 5, 3, 1, 1 ]

# In this example there are two admissible transversals

# trans1:=AdmTransversals(3,5,[])[1];
# trans2:=AdmTransversals(3,5,[])[2];
# l:=Length(trans1);

# for i in [1..l] do 
# 	Print("lamb= ",trans1[i], ".....m(lamb)= ", MullineuxMap(3,trans1[i]), "...", trans2[i],"\n");
# od;

#  % lamb= [ 7, 4, 2, 2 ].....m(lamb)= [ 7, 3, 2, 2, 1 ]...[ 7, 4, 2, 2 ]
#  % lamb= [ 8, 3, 2, 1, 1 ].....m(lamb)= [ 6, 4, 3, 2 ]...[ 8, 3, 2, 1, 1 ]
#  % lamb= [ 6, 4, 3, 2 ].....m(lamb)= [ 8, 3, 2, 1, 1 ]...[ 6, 4, 3, 2 ]
#  % lamb= [ 8, 4, 2, 1 ].....m(lamb)= [ 6, 3, 3, 2, 1 ]...[ 8, 4, 2, 1 ]
#  % lamb= [ 8, 4, 2, 1 ].....m(lamb)= [ 6, 3, 3, 2, 1 ]...[ 8, 4, 2, 1 ]
#  % lamb= [ 8, 5, 2 ].....m(lamb)= [ 4, 4, 3, 2, 1, 1 ]...[ 8, 5, 2 ]
#  % lamb= [ 8, 5, 2 ].....m(lamb)= [ 4, 4, 3, 2, 1, 1 ]...[ 8, 5, 2 ]
#  % lamb= [ 9, 3, 2, 1 ].....m(lamb)= [ 6, 4, 4, 1 ]...[ 9, 3, 2, 1 ]
#  % lamb= [ 9, 3, 2, 1 ].....m(lamb)= [ 6, 4, 4, 1 ]...[ 9, 3, 2, 1 ]
#  % lamb= [ 9, 3, 3 ].....m(lamb)= [ 8, 4, 3 ]...[ 9, 3, 3 ]
# lamb= [ 9, 3, 3 ].....m(lamb)= [ 8, 4, 3 ]...[ 9, 3, 3 ]
# lamb= [ 9, 4, 1, 1 ].....m(lamb)= [ 5, 4, 4, 1, 1 ]...[ 9, 4, 1, 1 ]
# lamb= [ 9, 4, 1, 1 ].....m(lamb)= [ 5, 4, 4, 1, 1 ]...[ 9, 4, 1, 1 ]
# lamb= [ 9, 5, 1 ].....m(lamb)= [ 5, 4, 3, 2, 1 ]...[ 9, 5, 1 ]
# lamb= [ 9, 5, 1 ].....m(lamb)= [ 5, 4, 3, 2, 1 ]...[ 9, 5, 1 ]
# lamb= [ 9, 6 ].....m(lamb)= [ 5, 4, 3, 3 ]...[ 9, 6 ]
# lamb= [ 9, 6 ].....m(lamb)= [ 5, 4, 3, 3 ]...[ 9, 6 ]
# lamb= [ 10, 3, 2 ].....m(lamb)= [ 7, 4, 4 ]...[ 10, 3, 2 ]
# lamb= [ 10, 3, 2 ].....m(lamb)= [ 7, 4, 4 ]...[ 10, 3, 2 ]


# Looks for e-regular partitions \lambda such that
# both \lambda does not dominate m(\lambda) and 
# m(\lambda) does not dominate \lambda.
TestNotDominates:=function(e,m)
	local i,la1,la2,la ;

	for i in [1..m] do 
		for la in ERegularPartitions(e,i) do 
			la1:=la;
			la2:=MullineuxMap(e,la);
			if la1>la2 then         # for not testing twice
				if Dominates(la1,la2)=false and Dominates(la2,la1)=false then 
					Print(la,"\n");
				fi;
			fi;
		od;
	od;
end;

# TestNotDominates:=function(e,m)
# 	local i,la1,la2,la ;

# 	for i in [1..m] do 
# 	Print("i= ",i, "\n");
# 		for la in ERegularPartitions(e,i) do 
# 			la1:=la;
# 			la2:=MullineuxMap(e,la);
# 			if la1>la2 then         # for not testing twice
# 				Print(Dominates(la1,la2),".....",Dominates(la2,la1),"\n");
# 			fi;
# 		od;
# 	od;
# end;


# Returns a list of completely admissible transversals
# of the e-core of weight w and core core
ComplAdmTransversals:=function(e,w,core)
	local transvlist, transv, l, ok, i,j, resu;

	transvlist:=AdmTransversals(e,w,core);
	l:=Length(transvlist[1]);
	resu:=[];

	for transv in transvlist do
		ok:=1;
		i:=1;
		
		while ok=1 and i<=l do
			j:=1;
			while ok=1 and j<=l do 
				if Dominates(MullineuxMap(e,transv[j]),transv[i]) then 
					ok:=0;
				else 
					j:=j+1;
				fi;
			od;
			i:=i+1;
		od;

		if ok=1 then 
			Add(resu, transv);
		fi;
	od;

	return resu;
end;

# tests if there are (and how many) completely admissible
# transversals for e-cores up to rank m.
Test1CompltAdmTransversals:=function(e,m)
	local listcores,w,core;

	listcores:=ListECores(e,m);

	for core in listcores do
		for w in [1..6] do 
			if Length(ComplAdmTransversals(e,w,core))>0 then 
				Print("# of transv= ",Length(ComplAdmTransversals(e,w,core)),", weight= ",w,", core= ",core,"\n");
			fi;
		od;
	od;
end;

# tests how many completely admissible transversals
# for every e-core with e every odd up to the odd k
# and every e-core with rank up to m

#tested see file  Test1Proposition7Weight2(11,15)

Test1Proposition7Weight2:=function(k,m)
	local  odds ,e ,core, coreslist;

	odds:=List([1..((k-1)/2)],x->(2*x+1));

	for e in odds do 
		Print("odd: ",e,"\n");
		coreslist:=ListECores(e,m);

		for core in coreslist do 
			if Length(ComplAdmTransversals(e,2,core))=0 then 
				if core<>ConjugatePartition(core) then 
					Print("OK ",core,"\n");
				else Print("self-conj! ",core, "\n");
				fi;
			fi;
			#Print(Length(ComplAdmTransversals(e,2,core)),"...",core,"\n"); #Option programme original
		od;
	od;
end;

# tests how many completely admissible transversals
# for every e-core with e every odd up to the odd k
# and every e-core with rank up to m
#tested see file  Test1Proposition7Weight2(11,15)
Test1Proposition7Weight4:=function(k,m)
	local  odds ,e ,core, coreslist;

	odds:=List([1..((k-1)/2)],x->(2*x+1));

	for e in odds do 
		Print("odd: ",e,"\n");
		coreslist:=ListECores(e,m);

		for core in coreslist do 
			# if Length(ComplAdmTransversals(e,4,core))=0 then 
			# 	if core<>ConjugatePartition(core) then 
			# 		Print("OK ",core,"\n");
			# 	else Print("self-conj! ",core, "\n");
			# 	fi;
			# fi;
			Print(Length(ComplAdmTransversals(e,4,core)),"...",core,"\n"); #Option programme original
		od;
	od;
end;

# pour p=3 il y a toujours des transv. compl. admissible, testé 
# jusqu'à m=40
Test1Proposition7Weight2E3:=function(m)
	local  e ,core, coreslist;
	coreslist:=ListECores(3,m);

		for core in coreslist do 
			# if Length(ComplAdmTransversals(3,2,core))=0 then 
			# 	if core<>ConjugatePartition(core) then 
			# 		Print("OK ",core,"\n");
			# 	else Print("self-conj! ",core, "\n");
			# 	fi;
			# fi;
			Print(Length(ComplAdmTransversals(3,2,core)),"...",core,"\n"); #Option programme original
		od;
	
end;

# Pour example particulier e=5 core=221
# qui n'a pas de transversal completement admissible

# list:=AdmTransversals(5,2,[2,2,1])[1];
# #[ [ 7, 3, 3, 2 ], [ 7, 5, 3 ], [ 7, 7, 1 ], [ 9, 3, 3 ], [ 11, 3, 1 ], 
# #  [ 12, 2, 1 ], [ 6, 4, 3, 1, 1 ], [ 7, 4, 3, 1 ], [ 8, 2, 2, 1, 1, 1 ], 
# #  [ 8, 3, 3, 1 ], [ 8, 4, 3 ], [ 8, 7 ], [ 11, 4 ], [ 13, 2 ] ]
# l:=14;


# for la in list do 
# 	for mu in list do 
# 		if Dominates(MullineuxMap(5,mu),la) then 
# 			Print(MullineuxMap(5,mu),"...",la,"\n");
# 		fi;
# 	od;
# od;

# Returns a list of all the possible compatible
# transversals for the e-block of weight w of the
# block corresponding to the core core.
CompTransversals:=function(e,w,core)
	local res, halflist, la, paire, size, transv,NEWtransv,inpair,
	x,i,mu,newx,SM,SIZEsm,compatiblepairs, ok,j,firts, second,pair,
	first, second;

	if w mod 2 = 1 then 
		return Print("That is an odd weight => there are no self-Mullineux \n partitions in that block. \n");
	
	elif core<>ConjugatePartition(core) then
		return Print("That is not a self-conjugate e-core \n there are no self-Mullineux partitions in that block. \n");

	else

		# (any) "half" of the p-regular partitions in the block
		# this was particularly chosen using the lex order.
		halflist:=[];
		SM:=[];
		for la in SSetReg(e,w,core) do 
			if la>MullineuxMap(e,la) then 
				Add(halflist,la);
			elif la=MullineuxMap(e,la) then 
				Add(SM,la);
			fi;
		od;
		size:=Length(halflist);
		SIZEsm:=Length(SM);


		compatiblepairs:=[];
		i:=1;
		ok:=1;

		while i<=size and ok=1 do 
			pair:=[];
			first:=0;
			second:=0;
			
			j:=1;
			while j<=SIZEsm and ok=1 do
				if first+1=j and Dominates(SM[j],halflist[i])=false then 
					first:=first+1;
				fi;
				if second+1=j and Dominates(SM[j],MullineuxMap(e,halflist[i]))=false then 
					second:=second+1;
				fi;
				if second<>j and first<>j then 
					ok:=0;
				fi;
				j:=j+1;
			od;

			if first=SIZEsm then 
				Add(pair,halflist[i]);
			fi;
			if second=SIZEsm then 
				Add(pair,MullineuxMap(e,halflist[i]));
			fi;
			if pair<>[] then 
			Add(compatiblepairs,pair);
			fi;
			i:=i+1;
		od;

		if Length(compatiblepairs)<>size then 
			transv:=[];
		else 
			if Length(compatiblepairs[1])=1 then
				transv:=[compatiblepairs[1]];
			else
				transv:=[[compatiblepairs[1][1]],[compatiblepairs[1][2]]];
			fi;

			i:=2;

			while Length(transv[1])<size do 
				NEWtransv:=[];
				
				for x in transv do 
					for mu in compatiblepairs[i] do
						newx:=Copy(x);
						Add(newx,mu);
						Add(NEWtransv,newx);
					od;
				od;

				transv:=NEWtransv;
				i:=i+1;
			od;
		fi;
		return transv;
	fi;
end;


# j'ai fait Test1Proposition14Weight2(15,20), souvent il y a deux transversales
# compatibles
Test1Proposition14Weight2:=function(k,m)
	local  odds ,e ,core, coreslist;

	odds:=List([1..((k-1)/2)],x->(2*x+1));

	for e in odds do 
		Print("odd: ",e,"\n");
		coreslist:=ListECoresSC(e,m);

		for core in coreslist do 
			Print(Length(CompTransversals(e,2,core)),"...",core,"\n"); 
		od;
	od;
end;

Test1Proposition14Weight4:=function(k,m)
	local  odds ,e ,core, coreslist;

	odds:=List([1..((k-1)/2)],x->(2*x+1));

	for e in odds do 
		Print("odd: ",e,"\n");
		coreslist:=ListECoresSC(e,m);

		for core in coreslist do 
			Print(Length(CompTransversals(e,4,core)),"...",core,"\n"); 
		od;
	od;
end;


Test1Proposition14Weight6:=function(k,m)
	local  odds ,e ,core, coreslist;

	odds:=List([1..((k-1)/2)],x->(2*x+1));

	for e in odds do 
		Print("odd: ",e,"\n");
		coreslist:=ListECoresSC(e,m);

		for core in coreslist do 
			Print(Length(CompTransversals(e,6,core)),"...",core,"\n"); 
		od;
	od;
end;