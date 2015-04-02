BeginPackage["XchainFactorization`"];

Unprotect[Evaluate[$Context<>"*"]];

FactorizationReset::usage="Restart the factorization, clear the storage of X-chain and corr group";

XResource::usage="Return the X-resource of correlation index c";
XResourceBinary::usage="Return the binary X-resource of correlation index c";
CorrelationIndex::usage="Return the correlation index of X-resource xi";
ParityOfXResource::usage="Return the parity of XResource";

Xchains::usage="Return the whole X-chains of G";
XchainGenerators::usage="Return the mutually not including X-chain generators of G";

CorrelationGroup::usage="Return the c-correlation group";
CorrelationGroupGenerators::usage="Return the correlation group generators";

NegParityXchainGenerators::usage="Return the X chian geneartors with negative parity";
FundamentalXGamma::usage="Return the fundamental Xbasis of graph";
XchainState::usage="Return the X-chain state of G with xi";
XchainStates::usage="Return the set of X-chain states of G";

GraphStateInX::usage="Return graph state represenation in X-basis";
GraphStateInZ::usage="Return graph state represenation in Z-basis";
CorrelationState::usage="Return Kappa-correlation state of a graph state";

SchmidtDecompCorrGroups::usage="Return the correlation group for Schmidt decomposition of graph state regarding the bipartition A|B";
SchmidtVectors::usage="Return the Schmidt vector of graph state regarding the bipartition A|B";
SchmidtDecompOfGraphState::usage="Return the Schmidt decomposition of graph state regarding the bipartition A|B";

GroupOfGenerators::usage="Return the group from a generating set";
GeneratorsOfGroup::usage="Return the generating set of a group";
SetOfBinaryIndex;
BinaryIndexOfSet;
HadarmardMatrix::usage="Return Hadarmard matrix for n qubits";
GlobalPhase::usage="The sign of the global phase correction";

GraphSymmetricDifference::usage="Symmetric difference of two graph states";
ZBiasDegree::usage="Z-bias degree of a graph state";
GraphStateOverlap::usage="Overlap of two graph states";
Begin["`Private`"];

$XchainsStored = False;
$Xchains = {};
$globalPhaseCorrection=False;
$globalPhase=1;
$XchainGroupStored = False;
$XchainGenerators = {};
$CorrGroupGeneratorsStored = False;
$CorrelationGroupGenerators = {};
$CorrelationGroupStored = False;
$CorrelationGroup = {};
$XchainStatesStored = False;
$XchainStates = {};
$ABcorrGroupStored = False;
$ABcorrGroup = {};
$ABcorrGroupGensStored = False;
$ABcorrGroupGens = {};

GlobalPhase[G_]:=Module[
	{},
	XchainStates[G];
	XchainFactorization`Private`$globalPhase
]

Options[FactorizationReset]:={CorrectGlobalPhase -> True };
FactorizationReset[OptionsPattern[]]:=Module[
	{},
	XchainFactorization`Private`$XchainsStored = False;
	XchainFactorization`Private`$Xchains = {};
	XchainFactorization`Private`$XchainGroupStored = False;
	XchainFactorization`Private`$XchainGenerators = {};
	XchainFactorization`Private`$CorrGroupGeneratorsStored = False;
    XchainFactorization`Private`$CorrelationGroupGenerators = {};
	XchainFactorization`Private`$XchainStatesStored = False;
	XchainFactorization`Private`$XchainStates = {};
	XchainFactorization`Private`$ABcorrGroupStored = False;
	XchainFactorization`Private`$ABcorrGroup = {};
	XchainFactorization`Private`$ABcorrGroupGensStored = False;
	XchainFactorization`Private`$ABcorrGroupGens = {};
	XchainFactorization`Private`$globalPhaseCorrection = OptionValue[CorrectGlobalPhase];
	XchainFactorization`Private`$globalPhase = 1;
];

HadarmardMatrix[n_]:=Nest[KroneckerProduct[{{1,1},{1,-1}},#]&,{1},n]/Power[2,n/2];

SymmetricDifference[a_,b_]:=Union[Complement[a,b],Complement[b,a]];
BinaryIndexOfSet[s_,n_]:=SparseArray[Table[p-> 1,{p,s}],{n}];
SetOfBinaryIndex[i_]:=Flatten[Position[i,1]];
Options[GroupOfGenerators]:={NeutralElement -> {}};
GroupOfGenerators[generators_, operation_,OptionsPattern[]]:=Table[
	Fold[operation[#1,#2]&, OptionValue[NeutralElement], genSet],
	{genSet,Subsets[generators]}
];
Options[GroupOfGenerators]:={NeutralElement -> {}, GroupDepth-> 2};
GeneratorsOfGroup[group_,operation_]:=Module[
	{genSet={}, groupTmp={}, groupTmp1, genNumber, i},

	If[Length[group]<2, Return[{}]];

	groupTmp = {#}&/@Union[group];
	genNumber=Log[OptionValue[GroupDepth],Length[groupTmp]];
	genSet = Append[ genSet, groupTmp[[2]][[1]] ];
	For[i=1,i<= Length[genSet],i++,
		groupTmp = Join[#[[1]],#[[2]]]&/@Gather[groupTmp, Union[Table[operation[m,genSet[[i]]],{m,#1}]]==Union[#2]&];
		If[Length[groupTmp]==1, Break[]];
		genSet = Append[genSet, groupTmp[[2]][[1]] ];
	];

	Union[genSet]
];
Options[XResourceBinary]:={};
XResourceBinary[G_,corrIndex_, OptionsPattern[]]:=Module[
	{
		c=corrIndex,adjM=AdjacencyMatrix[G], XchainGens, xOfc, XchainGroup, vertexN
	},
	vertexN = Length[adjM];
	XchainGens = NullSpace[adjM, Modulus->2];
	XchainGroup = GroupOfGenerators[XchainGens,BitXor,NeutralElement->ConstantArray[0,vertexN]];
	(*Check the existence of X-resource*)
	On[LinearSolve::nosol];
	xOfc = Check[LinearSolve[adjM, c, Modulus->2], False, LinearSolve::nosol];
	If[Not[xOfc], Return[{}]];
	If[XchainGroup=={},
		{xOfc},
		Table[BitXor[Xchain,xOfc],{Xchain, XchainGroup}]
	]
];

Options[XResource]:={Input-> "Set", Output->"Set"};
XResource[G_,corrIndex_, OptionsPattern[]]:=Module[
	{xOfc, cIndex=corrIndex, nV=VertexCount[G]},
	Switch[OptionValue[Input],
		"Set", cIndex = BinaryIndexOfSet[cIndex, nV],
		"Binary", cIndex = cIndex
	];
	xOfc = XResourceBinary[G,cIndex];
	Switch[OptionValue[Output],
		"Set", Table[SetOfBinaryIndex[x//Normal],{x,xOfc}],
		"Binary", xOfc
	]	
];

Options[CorrelationIndex]:={Input-> "Set", Output->"Set"};
CorrelationIndex[G_, xResource_, OptionsPattern[]]:=Module[
	{adjM = AdjacencyMatrix[G], nV=VertexCount[G], xi=xResource, cIndex},
	Switch[OptionValue[Input],
		"Set", xi = BinaryIndexOfSet[xi, nV],
		"Binary", xi = xi
	];
	cIndex = Mod[adjM.xi,2];
	Switch[OptionValue[Output],
		"Set", SetOfBinaryIndex[cIndex//Normal],
		"Binary", cIndex
	]
];

ParityOfXResource[G_,xi_]:=Power[-1,EdgeCount[Subgraph[G,xi]],2];

Options[Xchains]:={Output->"Set"};
Xchains[G_, OptionsPattern[]]:=Module[
	{nV=VertexCount[G]},
	XchainFactorization`Private`$Xchains = Union[XResource[G,{}]];
	XchainFactorization`Private`$XchainsStored = True;

	Switch[OptionValue[Output],
		"Set", XchainFactorization`Private`$Xchains,
		"Binary", 
			nV=VertexCount[G];
			BinaryIndexOfSet[#,nV]&/@XchainFactorization`Private`$Xchains
	]
];

Options[XchainGenerators]:={Output->"Set"};
XchainGenerators[G_, OptionsPattern[]]:=Module[
	{xChs, nV},
	If[XchainFactorization`Private`$XchainsStored,
		xChs =XchainFactorization`Private`$Xchains,
		xChs = Xchains[G]
	];
	XchainFactorization`Private`$XchainGenerators = GeneratorsOfGroup[xChs,SymmetricDifference];
	XchainFactorization`Private`$XchainGroupStored = True;
	
	Switch[OptionValue[Output],
		"Set", XchainFactorization`Private`$XchainGenerators,
		"Binary", 
			nV=VertexCount[G];
			BinaryIndexOfSet[#,nV]&/@XchainFactorization`Private`$XchainGenerators
	]
];

VForGenerators[gens_]:=Table[Block[{v},
		v = Complement[xi,Flatten[Complement[gens,{xi}]]];
		If[v=={},v=xi];
		v[[1]]
		]
	,
	{xi,gens}
	];
Options[CorrelationGroupGenerators]:={Output->"Set"};
CorrelationGroupGenerators[G_, OptionsPattern[]]:=Module[
	{vForXchains,xGens,n=VertexCount[G],cGroupGens},
	If[XchainFactorization`Private`$XchainGroupStored,
		xGens =XchainFactorization`Private`$XchainGenerators,
		xGens = XchainGenerators[G]
	];
	vForXchains = VForGenerators[xGens];
	cGroupGens = Complement[Range[n],vForXchains];
	cGroupGens = Table[{c},{c,cGroupGens}];

	XchainFactorization`Private`$CorrelationGroupGenerators = cGroupGens;
	XchainFactorization`Private`$CorrGroupGeneratorsStored = True;

	Switch[OptionValue[Output],
		"Set", XchainFactorization`Private`$CorrelationGroupGenerators,
		"Binary", 
			BinaryIndexOfSet[#,n]&/@XchainFactorization`Private`$CorrelationGroupGenerators
	]
];

QuotientGroup[gr_,subgr_]:=Module[
	{group=gr, subgroup = subgr, i, xi},
	group = Union[{{}},Complement[group, subgroup]];
	For[i=2,i<= Length[group],i++,
		xi=group[[i]];
		If[group==Union[Table[SymmetricDifference[xi,a],{a,group}]],Break[]];
		group=Union[Intersection[group, Table[SymmetricDifference[xi,a],{a,group}]]];
	];
	group
];

Options[CorrelationGroup]:={Output->"Set"};
CorrelationGroup[G_, OptionsPattern[]]:=Module[
	{nV=VertexCount[G], corrGens, cGroup},
	If[XchainFactorization`Private`$CorrGroupGeneratorsStored,
		corrGens =XchainFactorization`Private`$CorrelationGroupGenerators,
		corrGens = CorrelationGroupGenerators[G]
	];
	
	cGroup = GroupOfGenerators[corrGens, SymmetricDifference, NeutralElement->{}];
	XchainFactorization`Private`$CorrelationGroup = cGroup;
	XchainFactorization`Private`$CorrelationGroupStored = True;

	Switch[OptionValue[Output],
		"Set", XchainFactorization`Private`$CorrelationGroup,
		"Binary", 
			BinaryIndexOfSet[#,nV]&/@XchainFactorization`Private`$CorrelationGroup
	]
]

Options[NegParityXchainGenerators]:={Output->"Set"};
NegParityXchainGenerators[G_, OptionsPattern[]]:=Module[
	{negParityXchains, xGens, nV},
	If[XchainFactorization`Private`$XchainGroupStored,
		xGens =XchainFactorization`Private`$XchainGenerators,
		xGens = XchainGenerators[G]
	];
	negParityXchains=Select[xGens,ParityOfXResource[G,#]==-1&];

	Switch[OptionValue[Output],
		"Set", negParityXchains,
		"Binary", 
			nV=VertexCount[G];
			BinaryIndexOfSet[#,nV]&/@negParityXchains
	]
];

Options[FundamentalXGamma]:={Output->"Set"};
FundamentalXGamma[G_, OptionsPattern[]]:=Module[
	{negParityXchains, xGens, vNegParity, nV},
	If[XchainFactorization`Private`$XchainGroupStored,
		xGens =XchainFactorization`Private`$XchainGenerators,
		xGens = XchainGenerators[G]
	];
	negParityXchains=NegParityXchainGenerators[G];
	vNegParity = VForGenerators[negParityXchains];
	Switch[OptionValue[Output],
		"Set", vNegParity,
		"Binary", 
			nV=VertexCount[G];
			BinaryIndexOfSet[vNegParity,nV]
	]
];

RawDataToBraket[data_]:=Module[
	{compBasis},
	compBasis = data[[1]]*("|"<>StringJoin[ToString/@data[[2]]]<>"\[RightAngleBracket]");
	compBasis
];

Options[XchainState]:={Input->"Set", Output->"Raw"};
XchainState[G_, xResource_, OptionsPattern[]]:=Module[
	{xGamma, adjM=AdjacencyMatrix[G], xi=xResource, xIndex, nV=VertexCount[G], xState},
	Switch[OptionValue[Input],
		"Set", xi = xi,
		"Binary", xi = SetOfBinaryIndex[xi]
	];

	xGamma = FundamentalXGamma[G];
	xIndex = BitXor[BinaryIndexOfSet[xGamma,nV], adjM.BinaryIndexOfSet[xi,nV]];
	xIndex = Mod[xIndex,2];
	xState = {ParityOfXResource[G,xi], xIndex};
	Switch[OptionValue[Output],
		"Raw", xState,
		"Braket", RawDataToBraket[xState]
	]
];

Options[XchainStates]:={Output->"Raw"};
XchainStates[G_, OptionsPattern[]]:=Module[
	{cGroupGens, cGroup, nV=VertexCount[G], xStates, globalPhase},
	If[XchainFactorization`Private`$CorrGroupGeneratorsStored,
		cGroupGens =XchainFactorization`Private`$CorrelationGroupGenerators,
		cGroupGens = CorrelationGroupGenerators[G]
	];
	cGroup = GroupOfGenerators[cGroupGens,SymmetricDifference];
	xStates = Table[Join[XchainState[G,xi],{xi}],{xi,cGroup}];

	If[Total[xStates[[All,1]]]>= 0,
		globalPhase=1,
		globalPhase=-1
		(*xStates = Table[{globalPhase*s[[1]],s[[2]],s[[3]]},{s,xStates}];*)
	];

	If[XchainFactorization`Private`$globalPhaseCorrection==True,
		XchainFactorization`Private`$globalPhase = globalPhase
	];
	XchainFactorization`Private`$XchainStates = xStates;
	XchainFactorization`Private`$XchainStatesStored = True;

	Switch[OptionValue[Output],
		"Raw", XchainFactorization`Private`$XchainStates,
		"Braket", Table[{RawDataToBraket[xState],xState[[3]]},{xState,XchainFactorization`Private`$XchainStates}]
	]
];

Options[SuperpositionOfxStates]:={Output->"Vector"};
SuperpositionOfxStates[states_, OptionsPattern[]]:=Module[
	{nV, endState, stateSet=states},
	nV=Length[states[[1,2]]];
	Switch[OptionValue[Output],
		"Vector", 
			stateSet = Table[FromDigits[Normal[xs[[2]]],2]+1 -> xs[[1]],{xs,stateSet}];
			endState = SparseArray[stateSet,{Power[2,nV]}]/Sqrt[Length[stateSet]],
		"Braket", 
(*
			coeffSet = Table[{xs[[1]],ToString[IntegerString[FromDigits[Normal[xs[[2]]],2],2,nV]]},{xs,states}];
			coeffSet = Table[Sign[c[[1]]](If[Abs[c[[1]]]!= 1,ToString[Abs[c[[1]]],StandardForm],""]<>"\[LeftBracketingBar]"<>ToString[c[[2]],StandardForm]<>"\[RightAngleBracket]"),{c,coeffSet}];
			endState = 1/Sqrt[Length[states]]*(Total[coeffSet])
*)
			stateSet = RawDataToBraket/@stateSet;
			endState = 1/Sqrt[Length[states]]*(Total[stateSet])
	];
	endState
];

Options[GraphStateInX]:={Output->"Vector"};
GraphStateInX[G_,OptionsPattern[]]:=Module[
	{xStates, coeffSet, nV=VertexCount[G], gState, globalPhase},
	If[XchainFactorization`Private`$XchainStatesStored,
		xStates =XchainFactorization`Private`$XchainStates,
		xStates = XchainStates[G]
	];
	If[Total[xStates[[All,1]]]>= 0,
		globalPhase=1,
		globalPhase=-1;
	];
	gState = SuperpositionOfxStates[xStates, Output->OptionValue[Output]];

	XchainFactorization`Private`$globalPhase*gState
];

Options[GraphStateInZ]:={Output->"Vector"};
GraphStateInZ[G_,OptionsPattern[]]:=Module[
	{nV=VertexCount[G], vSubsets, zStates, coeffSet, gState},
	vSubsets = Subsets[Range[nV]];
	zStates = Table[{ParityOfXResource[G,vSet],BinaryIndexOfSet[vSet,nV]},{vSet, vSubsets}];
	gState = SuperpositionOfxStates[zStates, Output->OptionValue[Output]];
	gState		
];

Options[CorrelationState]:={Input->"Generators", Output->"Vector"};
CorrelationState[G_, corrGrGens_, OptionsPattern[]]:=Module[
	{corrGroup, xStates, cStates, cState},
	Switch[OptionValue[Input],
		"Generators", corrGroup = GroupOfGenerators[corrGrGens, SymmetricDifference, NeutralElement->{}],
		"Group", corrGroup = corrGrGens
	];

	(*corrGroup = Table[BinaryIndexOfSet[c],{c, corrGroup}];*)
	If[XchainFactorization`Private`$XchainStatesStored,
		xStates =XchainFactorization`Private`$XchainStates,
		xStates = XchainStates[G]
	];
	
	cStates = Select[xStates,MemberQ[corrGroup,#[[3]]]&];
	
	cState = SuperpositionOfxStates[cStates, Output->OptionValue[Output]];
	cState
];

Options[SchmidtDecompCorrGroups]:={ReturnGenerator -> True};
SchmidtDecompCorrGroups[G_, A_, OptionsPattern[]]:=Module[
	{   
		xStates, nV=VertexCount[G], cGensInA, B,
		cGroupGens, cGroup,
		xChs,
		KappaA, KappaAGroup,
		KappaAA, KappaAAGroup, 
		KappaAsimB, KappaAsimBGroup,
		KappaB, KappaBGroup,
		KappaAsepB, 
		KappaAtoB, KappaAtoBGroup,
		adjM=AdjacencyMatrix[G]
	},
	B = Complement[Range[nV], A];
    If[XchainFactorization`Private`$XchainsStored,
		xChs =XchainFactorization`Private`$Xchains,
		xChs = Xchains[G]
	];
	If[XchainFactorization`Private`$XchainStatesStored,
		xStates =XchainFactorization`Private`$XchainStates,
		xStates = XchainStates[G]
	];
	If[XchainFactorization`Private`$CorrGroupGeneratorsStored,
		cGroupGens =XchainFactorization`Private`$CorrelationGroupGenerators,
		cGroupGens = CorrelationGroupGenerators[G]
	];
	cGroup = GroupOfGenerators[cGroupGens, SymmetricDifference];
(*
	cGensInA = Table[{c}, {c,Intersection[Flatten[cGroupGens],A]}];
*)
	KappaA = Table[SetOfBinaryIndex[x],{x,NullSpace[adjM[[B]],Modulus->2]}];
	KappaAGroup = GroupOfGenerators[KappaA, SymmetricDifference];
	KappaAGroup = Intersection[cGroup,KappaAGroup];
	KappaA = GeneratorsOfGroup[KappaAGroup,SymmetricDifference];
	KappaAA = Select[KappaA,Intersection[#,A]==#&];
	KappaAAGroup = GroupOfGenerators[KappaAA, SymmetricDifference];

	KappaB = Table[SetOfBinaryIndex[x],{x,NullSpace[adjM[[A]],Modulus->2]}];
	KappaBGroup = GroupOfGenerators[KappaB, SymmetricDifference];
	KappaBGroup = Intersection[cGroup,KappaBGroup];
	KappaB = GeneratorsOfGroup[KappaBGroup,SymmetricDifference];
	
	KappaAsimB = Complement[KappaA, KappaAA];
	KappaAsimBGroup = GroupOfGenerators[KappaAsimB, SymmetricDifference];
	KappaAsimBGroup = Select[KappaAsimBGroup, XiSimBQ[G,#,KappaBGroup]&];
	KappaAsimB= GeneratorsOfGroup[KappaAsimBGroup,SymmetricDifference];

	KappaAtoBGroup = QuotientGroup[cGroup, GroupOfGenerators[Union[KappaAA, KappaAsimB, KappaB],SymmetricDifference]];
	KappaAtoB= GeneratorsOfGroup[KappaAtoBGroup,SymmetricDifference];

	XchainFactorization`Private`$ABcorrGroup = {KappaAAGroup,KappaAsimBGroup,KappaBGroup,KappaAtoBGroup};
	XchainFactorization`Private`$ABcorrGroupStored = True;
	XchainFactorization`Private`$ABcorrGroupGens = {KappaAA, KappaAsimB, KappaB, KappaAtoB};
	XchainFactorization`Private`$ABcorrGroupGensStored = True;
	
	If[OptionValue[ReturnGenerator],
		XchainFactorization`Private`$ABcorrGroupGens,
		XchainFactorization`Private`$ABcorrGroup
	]
];
XiSimBQ[G_, xi_, KappaBGroup_]:=Module[
	{edges, i, result = True, KappaBGr = KappaBGroup},
	KappaBGr = Complement[KappaBGr,{{}}];
	For[i=1,i<= Length[KappaBGr]&&Length[xi]>0,i++,
		edges=Table[e[[1]]\[UndirectedEdge]e[[2]],{e,Tuples[{xi,KappaBGr[[i]]}]}];
		edges=Fold[#1|#2&,edges[[1]],edges];
		If[Not[EvenQ[Length[EdgeList[G,edges]]]], result=False;Break[]];
	];
	result
];

Options[SchmidtVectors]:={Output->"Vector", AtoBcorrIndex-> All};
SchmidtVectors[G_, A_, OptionsPattern[]]:=Module[
	{
	nV=VertexCount[G], B,
	corrGroup, xStates, cStates, cState, ABcorrGroup, 
	KappaAGroup, KappaAGroupXi, KappaAStates,
	KappaBGroup, KappaBGrouppXi, KappaBStates,
	KappaAtoBGroup, AtoBGroupSelected,
	sVectors
	},

	B=Complement[Range[nV],A];

	If[XchainFactorization`Private`$XchainStatesStored,
		xStates =XchainFactorization`Private`$XchainStates,
		xStates = XchainStates[G]
	];

	If[XchainFactorization`Private`$ABcorrGroupStored,
		ABcorrGroup =XchainFactorization`Private`$ABcorrGroup,
		ABcorrGroup = SchmidtDecompCorrGroups[G, A, ReturnGenerator->False]
	];
	KappaAGroup =  Flatten[ABcorrGroup[[{1,2}]],1];
	KappaBGroup = ABcorrGroup[[3]];
	KappaAtoBGroup = ABcorrGroup[[4]];
	
	If[OptionValue[AtoBcorrIndex]==All, AtoBGroupSelected=KappaAtoBGroup, AtoBGroupSelected=OptionValue[AtoBcorrIndex]];
	
	sVectors=Table[
	  Block[{},
		KappaAGroupXi = Table[SymmetricDifference[xi,k],{k,KappaAGroup}];
		KappaAStates = Select[xStates,MemberQ[KappaAGroupXi,#[[3]]]&];
		KappaAStates = Table[{x[[1]],x[[2]][[A]],x[[3]]},{x,KappaAStates}];

		KappaBGrouppXi = Table[SymmetricDifference[xi,k],{k,KappaBGroup}];
		KappaBStates = Select[xStates,MemberQ[KappaBGrouppXi,#[[3]]]&];
		KappaBStates = Table[{x[[1]],x[[2]][[B]],x[[3]]},{x,KappaBStates}];

		KappaAStates = SuperpositionOfxStates[KappaAStates, Output->OptionValue[Output]];
		KappaBStates = XchainFactorization`Private`$globalPhase*SuperpositionOfxStates[KappaBStates, Output->OptionValue[Output]];
		{ParityOfXResource[G,xi], KappaAStates,KappaBStates,xi}
	  ],
	  {xi, AtoBGroupSelected}
	];
	sVectors
];
SchmidtDecompOfGraphState[G_,A_]:=Module[
	{sVectors,nFactor},
	sVectors = SchmidtVectors[G,A,Output->"Braket"];
	nFactor = 1/Sqrt[Length[sVectors]];
	sVectors = Table[CircleTimes[v[[2]],v[[1]]*v[[3]]],{v,sVectors}];
	nFactor*(Total[sVectors])
];

ZBiasDegree[G_]:=Module[
	{xGens, negXGens, nV=VertexCount[G]},
	xGens=XchainGenerators[G];
	negXGens=NegParityXchainGenerators[G];
	If[Length[negXGens]>0,
		0,
		Power[2,-(nV-Length[xGens])/2]
	]
];
Options[GraphSymmetricDifference]:={};
GraphSymmetricDifference[G1_,G2_,OptionsPattern[]]:=GraphUnion[GraphDifference[G1,G2],GraphDifference[G2,G1]];
GraphStateOverlap[G1_,G2_]:=Module[{},
	ZBiasDegree[GraphSymmetricDifference[G1,G2]]
];

End[];

Protect[Evaluate[$Context<>"*"]];

EndPackage[];
