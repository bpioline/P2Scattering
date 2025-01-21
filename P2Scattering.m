(* ::Package:: *)

(*********************************************************************
 *
 *  P2Scattering.m 1.5         
 *                                                          
 *  Developed by Bruno Le Floch and Boris Pioline, October 2022-Jan 2025
 *
 *  Distributed under the terms of the GNU General Public License 
 *
 *  Release notes for 1.0.1-2: 
 * - renamed Slope into GenSlope
 * - included Needs["CoulombHiggs`"]
 * - introduced Trees[{r_,d_,chi_}] as list of precomputed trees
 * - introduced ShiftTree, TreeTop
 * 1.0.3 - 5
 * - changed output of BinaryConstituents
 * - Added ZLVch2
 * - included routines for McKay scattering diagram
 * - Flipped n1 and n2 in definition of (u,v) coordinates, added McKayRay
 * - Added McKayrep, McKayRayEq; pushed back origin of initial rays in McRayScattCheck
 * 1.0.6 -7:
 * - Added routines for Fundamental domains of Gamma_1(3)
 * - Added MonodromyOnTau, MonodromyOnCharge 
 * 1.0.8 - 9:
 * - Added Eichler integral computations
 * - added ch2tochi, chitoch2 (ChToChi, ChiToCh are obsolete)
 * - Modified ToFundDomainC,ToFundDomainO such that Im[tau] never vanishes
 * - Added FundDomain3
 * 1.0.10
 * - Added EichlerC, EichlerCp
 * - Added ToFundDomainOApprox, ToFundDomainCApprox, IntegralCurve, NormalizeFunctionDomain
 * 1.0.11
 * - Use ToFundDomainCApprox in EichlerZch2, added EichlerZch2LV, updated IntegralCurve
 * 1.0.12
 * - Add repCh2, ToFundDomainCSeq, Euler, ExcepToChi, Bruno's routines
 * 1.1
 * - Changes requested by Bruno
 * - Divided QuantumVolume by I such that it is real positive
 * - Added tauO,MLV,MCon,MOrb,MOrbp,gam1,gam2,gam3,gam1p,gam2p,gam3p
 * - Added FundDomainRulesC[k_] and similar for O,3; CriticalPsi
 * - Modified repCh, repCh2, TreeCharge, TreeChargech2
 * - Added DimMcKay
 * - Added CPointxy, and psi-dependent version of ScattDiag, ScattDiagInternal
 * - Added StabilityWall, DtauZ
 * - Flipped overall sign of gam1,gam1p,...
 * - Added ScattDiagLV, ScattDiagInternalLV, RequestHeight
 * - Incorporated InitialLabelPosition (previously RequestHeight) and TreeHue
 * 1.2
 * - Bruno's modifications
 * - Added McKayInitialRays
 * 1.3
 * - removed ChiToCh, ChToChi, FracPart
 * - renamed ChiToN,NToChi,repChN into chiton, ntochi, repChn
 * - renamed XyToSt, StToXy to xytost, sttoxy
 * - Added ScanAllTrees, WallLine
 * - renamed McKayListAllConsistentTrees into McKayScanAllTrees
 * - Added some routines from CoulombHiggs.m, prefaced by P2
 * - Renamed Trees[] into LVTrees[]
 * - Added Package IndexVars` to share variables with CoulombHiggs.m
 * - Changes in TreeToRaysPlot and TreeToRaysch2
 * - Fixed bug in ScanBinarySplits, changed its arguments
 * - Added constraint k[i]>=k[i-1] when m[i]==m[i-1] in ScanConstituents, similarly for kp
 * - Modified ListStableTreesPerturb such that only on chi is perturbed
 * 1.4
 * - Added BinaryTreeIndex,BinaryTreeIndexInternal,AbelianizedScatteringSequence,
 * - Added IndexFromAbelianizedSequences, IndexFromSequences
 * - Fixed ScanKroneckerSplits, ScanConstituents
 * 1-5
 * - Added ConstructMcKayDiagram, McKayTreesFromListRays, McKayScattIndexImproved, InitialRaysOrigin
 * - Added ConstructLVDiagram, LVTreesFromListRays, ScattIndexImproved, ScattIndexImprovedInternal, CostPhi
 * - Added KroneckerDims, FOmbToOm
 *********************************************************************)
 
Print["P2Scattering 1.5 - A package for evaluating DT invariants on \!\(\*SubscriptBox[K,SuperscriptBox[\[DoubleStruckCapitalP],2]]\)"];


BeginPackage["IndexVars`"];
Protect[tau, y];
EndPackage[];

BeginPackage["P2Scattering`"]
Needs["IndexVars`"]



(* symbols *)
Ch::usage = "Ch[m] denotes the charge vector for O(m)";
Kr::usage = "\!\(\*SubscriptBox[\(Kr\), \(m_\)]\)[p_,q_] denotes the index of the Kronecker quiver with m arrows, dimension vector (p,q)";
\[Gamma]::usage = "\!\(\*SubscriptBox[\(\[Gamma]\), \(i\)]\) denotes the charge vector for the i-th node of the McKay quiver";
a::usage = "Parameter running from 0 to 1";
y::usage = "Refinement parameter";
tau::usage = "Kahler modulus"; 
tau1::usage = "Real part of tau";
tau2::usage = "Imaginary part of tau";
gam1::usage = "Charge vector [r,d,chi) for E1[-1]=Ch[0][-1]";
gam2::usage = "Charge vector [r,d,chi) for E2[-1]=Ch[-1/2][0]";
gam3::usage = "Charge vector [r,d,chi) for E3[-1]=Ch[-1][1]";

(* global variables *)
LVTrees::usage = "LVTrees[{r_,d_,chi_] gives the list of precomputed trees, when available";
McKayTrees::usage = "McKayTrees[{n1_,n2_,n3_] gives the list of precomputed McKay trees, when available";
ExcepSlopes::usage = "List of slopes of exceptional bundles between -3 and 4";
ListSubsetsAny::usage = "Precomputed list of all binary splits of Range[n] for n=2..10, used by ListStableTrees";
FourierC::usage = "List of the first 50 Fourier coefficients of C";
FourierCp::usage = "List of the first 50 Fourier coefficients of Cp";
QuantumVolume::usage = "Numerical value of V= 0.462758";
tauO::usage = "-1/2+I/(2Sqrt[3])";
Initialtau1::usage = "Initial value of tau1 for FindRoot";
Initialtau2::usage = "Initial value of tau2 for FindRoot";
MLV::usage = "Monodromy matrix around cusp at infinity";
MCon::usage = "Monodromy matrix around cusp at 0";
MOrb::usage = "Monodromy matrix around orbifold point tauO";
MOrbp::usage = "Monodromy matrix around orbifold point tauO+1";

(* Manipulating Chern vectors *)
Euler::usage = "Euler[{r_,d_,chi_},{rr_,dd_,cchi_}] computes the Euler form on D(P^2)";
DSZ::usage = "DSZ[{r_,d_,chi_},{rr_,dd_,cchi_}] computes the antisymmetrized Euler form 3(r dd-rr d) on D(P^2)";
Disc::usage = "Disc[{r_,d_,chi_}] computes the discriminant d^2-2r(chi-r-3/2 d))/(2r^2)";
Disch2::usage = "Disch2[{r_,d_,ch2_}] computes the discriminant (d^2-2r ch2)/(2r^2)";
DiscR::usage = "DisR[{r_,d_,chi_}] computes the rescaled discriminant d^2-2r(chi-r-3/2 d)";
GenSlope::usage = "GenSlope[{r_,d_,chi_}] computes the slope d/r if r<>0, or (chi/d-3/2) if r=0";
DimGieseker::usage = "DimGieseker[{r_,c1_,chi_}]Computes expected dimension of moduli space of Gieseker-semi stable sheaves";
ch2tochi::usage = "ch2tochi[{r_,d_,ch2_}] produces corresponding {r,d,chi}";
chitoch2::usage = "chitoch2[{r_,d_,chi_}] produces corresponding {r,d,ch2}";
SpecFlow::usage = "SpecFlow[{r_,d_,chi_},eps_]:= computes the charge vector {rr,dd,cchi} for E x O(eps)";
SpecFlowch2::usage = "SpecFlow[{r_,d_,ch2_},eps_]:= computes the charge vector {rr,dd,cch2} for E x O(eps)";
repCh::usage = "Replacement rule mapping Ch[tau1] or Ch[tau1][homshift] to their charge vector {r,d,chi}";
repCh2::usage = "Replacement rule mapping Ch[tau1] or Ch[tau1][homshift] to their charge vector {r,d,ch2}";
repChO::usage = "replaces Ch[m_] by string O(m)";
repKr::usage = "replaces \!\(\*SubscriptBox[\(Kr\), \(m_\)]\)[p_,q_]\[RuleDelayed]1";

(* Le Potier curve *)
LPCurve::usage = "LPCurve[mu_]:= computes the Drezet-Le Potier curve delta(mu)";
FracPart::usage = "FracPart[x_]:= x - Ceiling[x]"; 
ExcepToChi::usage = "ExcepToChi[mu_] gives the Chern vector [r,d,chi) of exceptional bundle of slope mu";

(* Large volume central charge, walls of marginal stability *)
ZLV::usage = "ZLV[{r_,d_,chi_},{s_,t_}] computes the standard central charge -1/2 r (s+I t)^2+d (s+I t)+r+3d/2-chi";
ZLVch2::usage = "ZLVch2[{r_,d_,ch2_},{s_,t_}] computes the central charge -1/2 r (s+I t)^2+d (s+I t)-ch2";
Wall::usage = "Wall[{r_,d_,chi_},{rr_,dd_,cchi_},{s_,t_}] computes Im[Z[gamma] Conjugate[Z[ggamma]]";
Wallch2::usage = "Wallch2[{r_,d_,ch2_},{rr_,dd_,cch2_},{s_,t_}] computes Im[Z[gamma] Conjugate[Z[ggamma]]";

(* basic operations on trees and lists of trees *)
TreeCharge::usage = "TreeCharge[tree_] is the total charge {r,d,chi} carried by tree (or list of trees).";
TreeChargech2::usage = "TreeChargech2[tree_] is the total charge {r,d,ch2} carried by tree (or list of trees).";
TreeTop::usage = "TreeTop[Tree_] computes the (s,t) coordinate of the root of the tree";
TreeConstituents::usage = "TreeConstituents[Tree_] gives the flattened list of constituents of Tree";
FlipTree::usage = "FlipTree[Tree_] constructs the reflected tree under Ch[m]:>-Ch[-m]";
ShiftTree::usage = "ShiftTree[Tree_,k_] constructs the shifted tree under Ch[m]:>-Ch[m+k]";
ScattCheck::usage = "ScattCheck[Tree_]returns {charge,{x,y}} of the root vertex if Tree is consistent, otherwise {total charge,{}}";
ScattSort::usage = "ScattSort[LiTree_] sorts trees in LiTree by growing radius";
ScattGraph::usage = "ScattGraph[Tree_] extracts the list of vertices and adjacency matrix of Tree";

(* local scattering using large volume central charge *)
xytost::usage = "xytost[{x_,y_}]:={x,Sqrt[x^2+2y]}";
sttoxy::usage = "sttoxy[{s_,t_}]:={s,-1/2(s^2-t^2)}";
xytosq::usage = "xytosq[{x_,y_}]:={x,y+x^2}";
IntersectRays::usage = "IntersectRays[{r_,d_,chi_},{rr_,dd_,cchi_}] returns intersection point (x,y) of two rays, or {} if they are collinear;
  IntersectRays[{r_,d_,chi_},{rr_,dd_,cchi_},z_,zz_]returns intersection point (x,y) of two rays if the intersection point lies upward from z and z', or {} otherwise";  
IntersectRaysSt::usage = "IntersectRaysSt[{r_,d_,chi_},{rr_,dd_,cchi_},psi_] returns intersection point (s,t) for rotated scattering rays, or {} if they are collinear";
TestBranch::usage = "TestBranch[{r_,d_,chi_},s_]  tests if (s,.) is on the branch with ImZ>0";
Rayt::usage = "Rayt[{r_,d_,chi_},s_,psi_] computes  t(s) for the ray Re[E^(-I psi) Z_gam]\[Equal]0 with LV central charge"; 
Rays::usage = "Rays[{r_,d_,chi_},t_,psi_] computes  s(t) for the ray Re[E^(-I psi) Z_gam]\[Equal]0 with LV central charge"; 
Raytch2::usage = "Raytch2[{r_,d_,ch2_},s_,psi_] computes  t(s) for the ray Re[E^(-I psi) Z_gam]\[Equal]0 with LV central charge"; 
Raysch2::usage = "Raysch2[{r_,d_,ch2_},t_,psi_] computes  s(t) for the ray Re[E^(-I psi) Z_gam]\[Equal]0 with LV central charge"; 


(* constructing scattering trees *)
ListStableTrees::usage = "ListStableTrees[LiCh_,{s0_,t0_}] constructs consistent trees from constituents list LiCh={k_i Ch[m_i]}, which are stable at (s0,t0)";
ListStableTreesPerturb::usage = "ListStableTrees[LiCh_,{s0_,t0_}] constructs consistent trees from constituents list LiCh={k_i Ch[m_i]} which are stable at (s0,t0) after perturbing  the chi_i's";
ListStablePlanarTrees::usage = "ListStablePlanarTrees[LiCh_,{s0_,t0_}] constructs consistent planar trees from ordered constituents list LiCh={k_i Ch[m_i]}, which are stable at (s0,t0)";
ScanConstituents::usage = "ScanConstituents[gam_,{m0min_,m0max_},{nmin_,nmax_},phimax_] searches possible list of constituents  with slope in [m0min,m0max], number of constituents in [nmin,nmax], cost function less than phimax and charges adding up to gam";
ScanBinarySplits::usage = "ScanBinarySplits[{r_,d_,chi_},t_] produces list of {rr,dd,cchi} such that {r,d,chi} can split into {rr,dd,cchi}+{r-rr,d-dd,chi-cchi} along the ray with psi=0 starting at height t";
ScanKroneckerSplits::usage = "ScanKroneckerSplits[{r_,d_,chi_}] produces list of {-k' Ch(m'), k Ch(m)} such that each doublet adds up to {r,d,chi}";
ScanAllTrees::usage = "ScanAllTrees[{r_,d_,chi_},{s0_,t0_}] constructs all possible trees with charges adding up to [r,d,chi) leading to an outgoing ray through the point (s,t)";


(* computing the index *)
ScattIndex::usage = "ScattIndex[TreeList_] computes the index for each tree in TreeList; do not trust the result if internal lines have non-primitive charges";
ScattIndexInternal::usage = "ScattIndexInternal[Tree_] computes {total charge, list of Kronecker indices associated to each vertex in Tree}";
EvaluateKronecker::usage = "EvaluateKronecker[f_] replaces each \!\(\*SubscriptBox[\(Kr\), \(m_\)]\)[p_,q_] with the index of the Kronecker quiver with m arrows and dimension vector {p,q}, using CoulombHiggs package";
BinaryTreeIndex::usage="BinaryTreeIndex[TreeList_] computes the index of each binary tree in TreeList";
BinaryTreeIndexInternal::usage="BinaryTreeIndexInternal[Tree_] produces a list of wall-crossing factors from each vertex in a binary tree";
AbelianizedScatteringSequence::usage ="AbelianizedScatteringSequence[ScattSeq_] produces a list of abelianized constituents, by replacing each kO[m] by {k_i O[m]} where k_i runs over integer partitions of k";
IndexFromAbelianizedSequences::usage ="IndexFromAbelianizedSequences[LiAbelianized_,{s0_,t0_}] constructs all possible perturbed binary trees from constituents in LiAbelianized which are stable for ZLV[gam,{s0,t0}], and compute the contribution to the index from each of them";
IndexFromSequences::usage="IndexFromSequences[LiScattSeq_,{s0_,t0_}] constructs all possible lists of abelianized constituents from the list of scattering sequences LiScattSeq, removes duplicates, and applies IndexFromAbelianizedSequences on each of them";


(* plotting routines *)
TreeHue::usage= "TreeHue[i_,n_] specifies the color for the i-th tree among a list of n";
ScattDiag::usage= "ScattDiag[TreeList_] draws scattering diagram in (x,y) plane for each tree in Treelist"; 
ScattDiagOverlay::usage= "ScattDiagOverlay[TreeList_] overlays scattering diagrams in (x,y) plane for each tree in Treelist"; 
ScattDiagxy::usage= "ScattDiagxy[TreeList_,psi_] draws scattering diagrams in (x,y) plane overlaying each tree in Treelist, along with initial points"; 
ScattDiagInternal::usage= "ScattDiagInternal[Tree_] constructs total charge, coordinate of root and list of line segments in (x,y) coordinates, {min(x), max(x)}; used by ScattDiag"; 
ScattDiagSt::usage = "ScattDiagSt[TreeList_] overlays scattering diagrams in (s,t) plane for all trees in TreeList;
  ScattDiagSt[TreeList_,psi_] does the same for rotated scattering diagrams";
ScattDiagInternalSt::usage= "ScattDiagInternalSt[Tree_] constructs total charge, coordinate of root and list of line segments in (s,t) coordinates, {min(s), max(s)}; used by ScattDiag;
  ScattDiagInternalSt[Tree_,psi_] does the same for rotated scattering diagram"; 
ScattDiagLV::usage = "ScattDiagLV[TreeList_,psi_] overlays scattering diagrams in (s,t) plane for all trees in TreeList, using exact hyperbolaes for rays";
ScattDiagInternalLV::usage= "ScattDiagInternalSt[Tree,psi_,Styl_] constructs total charge, coordinate of root and list of line segments in (s,t) coordinates, {min(s), max(s)}, using PlotStyle->Styl for plotting rays ; used by ScattDiagLV;"; 
InitialLabelPosition::usage= "InitialLabelPosition[m_] returns a position (s,t) for the label for an initial ray with slope m; this position is updated on each call using variables LiSlopes and LiHeights"; 

ScattDiagLZ::usage = "ScattDiagLZ[TreeList_] overlays scattering diagrams in (s,q) plane for all trees in TreeList";
ScattPhi::usage = "ScattPhi[TreeList_] overlays scattering diagrams in (s,phi) plane for each tree in TreeList"; 
ScattPhiInternal::usage = "ScattPhiInternal[Tree_] compute {total charge, root coordinate, list of line segments in (s,phi) coordinates, {min(s), max(s)}";
PlotWallRay::usage = "PlotWallRay[{r_,d_,chi_},{rr_,dd_,cchi_},psi_,{L1_,L2_,H_}] plots the local scattering of (r,d,chi)->{rr,dd,cchi}+{r-rr,d-dd,chi-cchi} in range L1<s<L2, 0<t<H,  rotated by psi";
WallCircle::usage = "WallCircle[{r_,d_,chi_},{rr_,dd_,cchi_}] constructs the graphics directive for the wall of marginal stability in (s,t) plane";
WallLine::usage = "WallLine[{r_,d_,chi_},{rr_,dd_,cchi_}] constructs the graphics directive for the wall of marginal stability in (s,q) plane";


(* routines for McKay scattering diagram *)
chiton::usage = "chiton[{r_,d_,chi_}] produces the corresponding dimension vector {n1,n2,n3}";
ntochi::usage = "ntochi[{n1_,n2_,n3_}] produces the corresponding charge vector {r,d,chi}";
repChn::usage = "repChn transforms Ch[m_] into chiton[{1,m,1+m(m+3)/2}]}";
DimMcKay::usage = "DimMcKay[{n1_,n2_,n3_}] computes the dimension of quiver moduli space in anti-attractor chamber";
McKayrep::usage = "replaces {n1_,n2_,n3_} by n1 \!\(\*SubscriptBox[\(\[Gamma]\), \(1\)]\)+n2  \!\(\*SubscriptBox[\(\[Gamma]\), \(\(2\)\(\\\ \)\)]\)+n3 \!\(\*SubscriptBox[\(\[Gamma]\), \(3\)]\)";
McKayDSZ::usage = "McKayDSZ[{n1_,n2_,n3_},{nn1_,nn2_,nn3_}] computes the antisymmetrized Euler form";
McKayRayEq::usage = "McKayRayEq[{n1_,n2_,n3_},{u_,v_}] gives the linear form vanishing on the scattering ray";
McKayVec::usage = "McKayVec[{n1_,n2_,n3_}] computes the positive vector along the ray";
McKayRay::usage = "McKayRay[{n1_,n2_,n3_},{u_,v_},{k1_,k2_},tx_] produces from {u,v}+k1 vec to (u,v)+k2 vec, decorated with text at the target";
McKayScattIndex::usage = "McKayScattIndex[TreeList_] computes the index for each tree in TreeList; do not trust the result if internal lines have non-primitive charges";
McKayScattIndexInternal::usage = "McKayScattIndexInternal[Tree_] computes {total charge, list of Kronecker indices associated to each vertex in Tree}";
McKayScanAllTrees::usage = "McKayScanAllTrees[Nvec_] generates consistent scattering trees with leaves carrying charge {p,0,0}, {0,p,0},{0,0,p}, with non-zero DSZ pairing at each vertex, with distinct support";
McKayListAllTrees::usage = "McKayListAllTrees[Nvec_] generates all trees with leaves carrying charge {p,0,0}, {0,p,0},{0,0,p} and with non-zero DSZ pairing at each vertex ";
McKayScattCheck::usage = "McKayScattCheck[Tree_]returns {charge,{u,v}coordinate} of the root vertex if Tree is consistent, otherwise {total charge,{}}";
McKayScattGraph::usage = "McKayScattGraph[Tree_]extracts the list of vertices and adjacency matrix of Tree";
McKayScattDiag::usage= "McKayScattDiag[TreeList_] draws McKay scattering diagram in (u,v) plane for each tree in Treelist"; 
McKayScattDiagInternal::usage= "McKayScattDiagInternal[Tree_] constructs total charge, coordinate of root and list of line segments in (u,v) coordinates; used by McKayScattDiag"; 
McKayIntersectRays::usage = "McKayIntersectRays[{n1_,n2_,n3_},{nn1_,nn2_,nn3_}] returns intersection point (u,v) of two rays, or {} if they are collinear;
  McKayIntersectRays[{n1_,n2_,n3_},{nn1_,nn2_,nn3_},z_,zz_]returns intersection point (u,v) of two rays if the intersection point lies upward from z and z', or {} otherwise";
McKayInitialRays::usage="McKayInitialRays[psi_,L_] draws the initial rays in (u',v') plane, rescaling each arrow by a factor of L";


(* Fundamental domain of Gamma_1(3) *)
FundDomainO::usage = "FundDomainO[k_] produces the Graphics directives for the fundamental domain of Gamma_1(3) on the interval [-1/2+k,1/2+k]";
FundDomainC::usage = "FundDomainC[k_] produces the Graphics directives for the fundamental domain of Gamma_1(3) on the interval [k,k+1]";
FundDomain3::usage = "FundDomain3[k_] produces the Graphics directives for the fundamental domain of Gamma_1(3)+Z3 images on the interval [k,k+1]";
ToFundDomainO::usage = "ToFundDomainO[tau_] produces {tau',M'} such that M'.tau'=tau and tau' lies in fundamendal domain of Gamma_1(3) centered around orbifold";
ToFundDomainC::usage = "ToFundDomainC[tau_] produces {tau',M'} such that M'.tau'=tau and tau' lies in fundamendal domain of Gamma_1(3) centered around conifold";
ToFundDomainCSeq::usage = "ToFundDomainCSeq[tau_] produces {tau',M'} such that M'.tau'=tau and tau' lies in fundamendal domain of Gamma_1(3) centered around conifold, M is a string of U,V,T[m] generators";
ToFundDomainOApprox::usage = "ToFundDomainOApprox[tau_,precision_] produces {tau',M'} such that M'.tau'=tau and tau' lies in fundamendal domain of Gamma_1(3) centered around orbifold";
ToFundDomainCApprox::usage = "ToFundDomainCApprox[tau_,precision_] produces {tau',M'} such that M'.tau'=tau and tau' lies in fundamendal domain of Gamma_1(3) centered around conifold";
ApplyGamma13Lift::usage = "ApplyGamma13[M_,tau_] produces the image of tau under the lifted 3x3 matrix M";
MonodromyOnCharge::usage = "MonodromyOnCharge[M_,{r_,d_,chi_}] computes the image of charge vector under sequence of monodromies";
MonodromyOnTau::usage = "MonodromyOnTau[M_,tau_] computes the image of tau under sequence of monodromies";
FundDomainRulesC::usage = "FundDomainRulesC[k_] gives a list of rules tau->tau(a) for boundaries of FundDomainC[k] parametrized by 0<a<1";
FundDomainRulesO::usage = "FundDomainRulesO[k_] gives a list of rules tau->tau(a) for boundaries of FundDomainO[k] parametrized by 0<a<1";
FundDomainRules3::usage = "FundDomainRules3[k_] gives a list of rules tau->tau(a) for boundaries of FundDomain3[k] parametrized by 0<a<1";

(* Computing periods using Eichler integrals *)
EichlerC::usage= "EichlerC[tau_] computes C[tau]";
EichlerCp::usage= "EichlerCp[taup_] computes C'[taup]";
Eichlerf1::usage= "Eichlerf1[tau_]:=2Pi I(tau+1/2)+Eichlerf1b[tau]";
Eichlerf2::usage = "Eichlerf2[tau_]:=1/2 (2Pi I)^2(tau+1/2)^2+2Pi I(tau+1/2)Eichlerf1b[tau]+Eichlerf2b[tau]";
Eichlerf1b::usage = "Eichlerf1b[tau_]:=Sum[FourierC[[n+1]]/n Exp[2Pi I n tau],n>0]";
Eichlerf2b::usage ="Eichlerf2b[tau_]:=-Sum[FourierC[[n+1]]/n^2 Exp[2Pi I n tau],n>0]";
Eichlerf1p::usage = "Eichlerf1p[taup_]:=Sum[FourierCp[[n+1]]/n Exp[2Pi I n taup],n>0]";
Eichlerf2p::usage = "Eichlerf2p[taup_]:=2Pi I(taup)Eichlerf1p[taup]-Sum[FourierCp[[n+1]]/n^2 Exp[2Pi I n taup],n>0]";
EichlerTLV::usage= "EichlerTLV[tau_] gives numerical value of T[tau] using Eichler integral near LV point";
EichlerTDLV::usage= "EichlerTDLV[tau_] gives numerical value of T[tau] using Eichler integral near LV point";
EichlerTC::usage = "EichlerTC[tau_] gives numerical value of T[tau] using Eichler integral near conifold point";
EichlerTDC::usage = "EichlerTDC[tau_] gives numerical value of T[tau] using Eichler integral near conifold point";
EichlerZ::usage = "EichlerZ[{r_,d_,chi_},tau_] gives numerical value of central charge at tau=t1+I t2, by mapping back to fundamental domain F_C";
EichlerZch2::usage = "EichlerZch2[{r_,d_,ch2_},tau_] gives numerical value of central charge at tau=t1+I t2, by mapping back to fundamental domain F_C";
EichlerZch2LV::usage = "EichlerZch2LV[{r_,d_,ch2_},tau_] gives numerical value of central charge at tau=t1+I t2, using Eichler integral at large volume";
EichlerT::usage= "EichlerT[tau_] gives numerical value of T[tau] using Eichler integral, by mapping back to fundamental domain F_C";
EichlerTD::usage= "EichlerTD[tau_] gives numerical value of TD[tau] using Eichler integral, by mapping back to fundamental domain F_C";
EichlerTtilde::usage= "EichlerTtilde[tau_] gives numerical value of Ttilde=(T-1/2)/(2Sqrt[3]) using Eichler integral, by mapping back to fundamental domain F_C";
EichlerTDtilde::usage= "EichlerTDtilde[tau_] gives numerical value of TDtilde=TD-1/2T-1/12 using Eichler integral, by mapping back to fundamental domain F_C";

IntersectExactRaysLV::usage="IntersectExactRaysLV[{r_,d_,chi_},{rr_,dd_,cchi_},psi_]returns value of tau of intersection point of two exact rays using EichlerTLV to evaluate the periods, or 0 if they are collinear";
IntersectExactRaysC::usage="IntersectExactRaysC[{r_,d_,chi_},{rr_,dd_,cchi_},psi_]  returns value of tau of intersection point of two exact rays using EichlerTC to evaluate the periods, or 0 if they are collinear";
CriticalPsi::usage = "CriticalPsi[mu_]:=ArcTan[mu/QuantumVolume]";
XY::usage = "XY[tau_,psi_] computes the coordinates {x,y} such that scattering  rays are straight lines ry+dx-ch2=0";

(* from Bruno *)
IntegralCurve::usage="IntegralCurve[tauinit_,tangent_,{ainit_,amin_,amax_},boundaries_] produces a function on [0,1] (it normalizes the domain).  Starting at tauinit at a=ainit, following the tangent direction (an expression in tau) and stopping at the boundaries (default: {Im[tau]==0.01}).  The range of integration parameters {amin,amax} can be infinite provided the actual rays remain finite by hitting the boundaries.";
NormalizeFunctionDomain::usage="NormalizeFunctionDomain[fun_InterpolatingFunction] rescales the argument of fun to interval [0,1]";
CPointchi::usage="CPointchi[tau_] gives the charge vector [r,d,chi) of an object that becomes massless at tau (rational).";
CPointch2::usage="CPointch2[tau_] gives the charge vector [r,d,ch2] of an object that becomes massless at tau (rational).";
CPointxy::usage="CPointxy[tau_,psi_] computes the (x,y) coordinate of initial point Ch[tau]";
ConifoldRay::usage="ConifoldRay[init_,psi_,homshift_] is the ray (complex-valued on [0,1]) starting at the rational number init=p/q (with q not divisible by 3)";
DtauT::usage="DtauT[\[Tau]_] is T'[\[Tau]], the derivative of T with respect to \[Tau], calculated efficiently.";
DtauZch2::usage="DtauZch2[\[Gamma]_,\[Tau]_] is \!\(\*SubscriptBox[\(Z\), \(\[Gamma]\)]\)'[\[Tau]], namely D[EichlerZch2[\[Gamma],\[Tau]],\[Tau]], calculated efficiently.";
DtauZ::usage="DtauZ[\[Gamma]_,\[Tau]_] is \!\(\*SubscriptBox[\(Z\), \(\[Gamma]\)]\)'[\[Tau]], namely D[EichlerZ[\[Gamma],\[Tau]],\[Tau]], calculated efficiently.";
UnitDtauZ::usage="UnitDtauZ[\[Gamma]_,\[Tau]_] is Normalize[\!\(\*SubscriptBox[\(Z\), \(\[Gamma]\)]\)'[\[Tau]]].";

ArgDtauT::usage="ArgDtauT[\[Tau]_] is the argument of T'[\[Tau]], between -Pi and Pi.";
ArgDtauTD::usage="ArgDtauTD[\[Tau]_] is the argument of \!\(\*SubscriptBox[\(T\), \(D\)]\)'[\[Tau]], between -Pi and Pi.";
ArgDtauZch2::usage="ArgDtauZch2[\[Gamma]_,\[Tau]_] is the argument of \!\(\*SubscriptBox[\(Z\), \(\[Gamma]\)]\)'[\[Tau]], between -Pi and Pi.";
UnitDtauT::usage="UnitDtauT[\[Tau]_] is Normalize[T'[\[Tau]]], namely T'[\[Tau]]/Abs[T'[\[Tau]]].";
UnitDtauTD::usage="UnitDtauTD[\[Tau]_] is Normalize[\!\(\*SubscriptBox[\(T\), \(D\)]\)'[\[Tau]]].";
UnitDtauZch2::usage="UnitDtauZch2[\[Gamma]_,\[Tau]_] is Normalize[\!\(\*SubscriptBox[\(Z\), \(\[Gamma]\)]\)'[\[Tau]]].";
NormalizeApprox::usage="NormalizeApprox[z_,eps_] normalizes z\[Element]\!\(\*TemplateBox[{},\n\"Complexes\"]\) (complex) to roughly unit length for large z, but behaves smoothly near zero.";
RayCh::usage="RayCh[\[Psi]_] gives an initial ray starting at 0, namely a function [0,1]\[RightArrow]\[DoubleStruckCapitalH] starting (close to) 0 and following a ray where \!\(\*SubscriptBox[\(Z\), \([1, 0, 0]\)]\)=-\!\(\*SubscriptBox[\(T\), \(D\)]\) has phase (\[Psi]+\[Pi]/2 mod \[Pi]).  Shifting \[Psi] by 2\[Pi] gives a different ray, corresponding to a homological shift by 2.  Values are cached.";
RayGeneralch2::usage="RayGeneralch2[\[Gamma]_,\[Psi]_,tauexpr_,start_List] gives a ray where \!\(\*SubscriptBox[\(Z\), \(\[Gamma]\)]\) has phase (\[Psi]+\[Pi]/2 mod \[Pi]).  The starting point is obtained using FindRoot[\!\(\*SubscriptBox[\(\[Ellipsis]Z\), \(\[Gamma]\)]\)[tauexpr]\[Ellipsis],start], see documentation of FindRoot.";
TotalChargech2::usage="TotalChargech2[tree_] gives the total charge vector [r,d,ch2] of a given tree (nested list).";
TotalChargechi::usage="TotalChargechi[tree_] gives the total charge vector [r,d,chi) of a given tree (nested list).";
TreeToRays::usage="TreeToRays[tree_,\[Psi]_] gives the (flat) list of rays (functions [0,1]\[RightArrow]\[DoubleStruckCapitalH] where Z has phase \[Psi](\[PlusMinus]?)\[Pi]/2 mod 2\[Pi]) of the binary tree.  The tree is given as a nested list of initial objects of the form (coef Ch[p/q][homshift]).";
TreeToRaysPlot::usage="TreeToRaysPlot[tree_,\[Psi]_,plotoptions___] plots the rays produced by TreeToRays[tree,\[Psi]], with the given plot options.";
RayFromInfinity::usage="RayFromInfinity[{r_,d_,chi_},psi_] (a function on [0,1]) is the ray of phase psi starting from the large volume limit";
StabilityWall::usage="StabilityWall[tree:{_,_},tauinit_,{amin_,amax_}] is a stability wall for the last fusion of the tree, as a function on [0,1].  The tree can also be a pair of charges.  The tauinit is used as a starting point of FindRoot along a vertical line.  The last argument can be omitted and defaults to {-2,2}; it is an interval around the starting point 0, and can be used to restrict the stability wall to only one side of tauinit.";


(* from CoulombHiggs *)
P2HiggsBranchFormula::usage = "P2HiggsBranchFormula[Mat_,Cvec_,Nvec_] computes the refined index of a quiver with DSZ matrix Mat, FI parameters Cvec, dimension vector Nvec using Reineke's formula. Assumes that the quiver has no oriented loops.";
P2RationalInvariant::usage = "P2RationalInvariant[Mat_,Cvec_,Nvec_,y_] computes the rational invariant of a quiver with DSZ matrix Mat, dimension vector Nvec and FI parameters Cvec computed using Reineke's formula.";
P2StackInvariant::usage = "P2StackInvariant[Mat_,Cvec_,Nvec_,y_] gives the stack invariant of a quiver with DSZ matrix Mat, dimension vector Nvec and FI parameters Cvec computed using Reineke's formula.";
P2QDeformedFactorial::usage = "P2QDeformedFactorial[n_,y_] gives the q-deformed factorial ";
P2ListAllPartitions::usage = "P2ListAllPartitions[gam_] returns the list of unordered partitions of the positive integer vector gam as a sum of positive integer vectors "; 
P2BinarySplits::usage="P2BinarySplits[Nvec_] gives the list of dimension vectors which are smaller than Nvec/2";


(* new routines in v1.5 *)
ConstructMcKayDiagram::usage="ConstructMcKayDiagram[Nmax_,ListRays_] constructs the quiver scattering diagram with height up to Nmax; The output consists of a list of  {charge, {u,v}, parent1, parent2,n1,n2}  with parent1=parent2=0 for initial rays; If ListRays is not empty, then uses it as initial rays.";
McKayTreesFromListRays::usage="McKayTreesFromListRays[ListRays_,{n1_,n2_,n3_}] extracts the list of distinct trees with given dimension vector";
McKayScattIndexImproved::usage="McKayScattIndexImproved[TreeList_, opt_] computes the index for each tree in TreeList, taking care of non-primitive internal states";
McKayScattIndexImprovedInternal::usage="McKayScattIndexImprovedInternal[Tree_, opt_] computes the index for Tree, taking care of non-primitive internal states";
InitialRaysOrigin::usage ="InitialRaysOrigin is a List of initial points (u_i,v_i) for initial rays in McKay scattering diagram";

ConstructLVDiagram::usage="ConstructLVDiagram[smin_,smax_,phimax_,Nm_,ListRays_] constructs the LV scattering diagram with initial rays O(k),O(k)[1] in the interval smin<=k<=smax, cost function up to phimax, scattering products with n1+n2<=Nm at each intersection; the output consists of a list of {charge, {x,y}, parent1,parent2,n1,n2}, with parent1=parent2=0 for initial rays; If ListRays is not empty, then uses it as initial rays."; LVTreesFromListRays::usage="lVTreesFromListRays[ListRays_,{r_,d_,chi_}] extract the trees with given charge in the List of rays,  by ConstructLVDiagram";
ScattIndexImproved::usage="ScattIndexImproved[TreeList_, opt_] computes the index for each tree in TreeList, taking care of non-primitive internal states";
ScattIndexImprovedInternal::usage="ScattIndexImprovedInternal[Tree_, opt_] computes the index for Tree, taking care of non-primitive internal states";
CostPhi::usage="CostPhi[{r_,d_,chi_},s_]:=d-r s";

KroneckerDims::usage="KroneckerDims[m_,Nn_] gives the list of populated dimension vectors {n1,n2} for Kronecker quiver with m arrows, with (n1,n2) coprime and 0<=n1+n2<=Nn"; 
FOmbToOm::usage="FOmbToOm[OmbList_] computes integer index from list of rational indices, used internally by FScattIndex";


(* ::Section:: *)
(*Global variables*)


tauO=-1/2+I/2/Sqrt[3];
MLV=\!\(\*
TagBox[
RowBox[{"(", GridBox[{
{"1", "0", "0"},
{"1", "1", "0"},
{
FractionBox["1", "2"], "1", "1"}
},
GridBoxAlignment->{"Columns" -> {{Center}}, "Rows" -> {{Baseline}}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.7]}, Offset[0.27999999999999997`]}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}}], ")"}],
Function[BoxForm`e$, MatrixForm[BoxForm`e$]]]\);MCon=\!\(\*
TagBox[
RowBox[{"(", GridBox[{
{"1", "0", "0"},
{"0", "1", 
RowBox[{"-", "3"}]},
{"0", "0", "1"}
},
GridBoxAlignment->{"Columns" -> {{Center}}, "Rows" -> {{Baseline}}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.7]}, Offset[0.27999999999999997`]}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}}], ")"}],
Function[BoxForm`e$, MatrixForm[BoxForm`e$]]]\);MOrb=\!\(\*
TagBox[
RowBox[{"(", GridBox[{
{"1", "0", "0"},
{
RowBox[{"-", 
FractionBox["1", "2"]}], 
RowBox[{"-", "2"}], 
RowBox[{"-", "3"}]},
{
FractionBox["1", "2"], "1", "1"}
},
GridBoxAlignment->{"Columns" -> {{Center}}, "Rows" -> {{Baseline}}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.7]}, Offset[0.27999999999999997`]}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}}], ")"}],
Function[BoxForm`e$, MatrixForm[BoxForm`e$]]]\);MOrbp=MLV . MOrb . Inverse[MLV];
(* [r,d,chi) for Ext-exceptional collection at tau_O *)
gam1=-{1,0,1};gam2={2,-1,0};gam3=-{1,-1,0};
(* [r,d,chi) for Ext-exceptional collection at tau_O'=tauO+1 *)
gam1p=-{1,1,3};gam2p={2,1,3};gam3p=-{1,0,1};


(* ::Section:: *)
(*Manipulating Chern vectors *)


Begin["`Private`"]

DSZ[{r_,d_,chi_},{rr_,dd_,cchi_}]:=3(r dd-rr d);
Euler[{r_,d_,chi_},{rr_,dd_,cchi_}]:=r rr+r(cchi-rr-3/2dd)+rr(chi-3/2d-r)-d dd+3/2(r dd-rr d);
Disc[{r_,d_,chi_}]:=(d^2-2r(chi-r-3/2 d))/(2r^2);
Disch2[{r_,d_,ch2_}]:=(d^2-2r ch2)/(2r^2);
DiscR[{r_,d_,chi_}]:=(d^2-2r(chi-r-3/2 d));
GenSlope[{r_,d_,chi_}]:=If[r!=0,d/r,If[d!=0,chi/d-3/2,0]];
DimGieseker[{r_,c1_,chi_}]:=c1^2-2r (chi-r-3/2 c1)-r^2+1;
ch2tochi[{r_,d_,ch2_}]:={r,d,r+3/2d+ch2};
chitoch2[{r_,d_,chi_}]:={r,d,chi-r-3/2d};
SpecFlow[{r_,d_,chi_},eps_]:={r,d+eps r,chi+3/2 r eps+eps d+r eps^2/2};
SpecFlowch2[{r_,d_,ch2_},eps_]:={r,d+eps r,ch2+eps d+r eps^2/2};
(* repCh={Ch[m_]:>{1,m,1+m (m+3)/2}};
repChPert={Ch[m_]:>{1,m,1+m (m+3)/2}+{0,0,1/20-1/100 m}};
repCh2={Ch[m_]:>{1,m,m^2/2}}; *)
(*We're making repCh and repCh2 complain when acting on things like Ch[1/3].*)
Ch::err = "The argument of Ch[`1`] has a denominator multiple of 3; it is a large volume point.";
repCh = {Ch[tau1 : _Integer | _Rational] | Ch[tau1 : _Integer | _Rational][homshift_] /;
     If[Mod[Denominator[tau1], 3] === 0, Message[Ch::err, tau1], True] :> (-1)^(0 + homshift) CPointchi[tau1]};
repCh2 = {Ch[tau1 : _Integer | _Rational] | Ch[tau1 : _Integer | _Rational][homshift_] /;
     If[Mod[Denominator[tau1], 3] === 0, Message[Ch::err, tau1], True] :> (-1)^(0 + homshift) CPointch2[tau1]};
repChO={Ch[m_]:>"O("<>ToString[m]<>")"};
repKr=Subscript[Kr, m_][p_,q_]:>1;


(* ::Section:: *)
(*Large volume central charge, walls of marginal stability*)


ZLV[{r_,d_,chi_},{s_,t_}]:=-1/2 (s+I t)^2 r+ (s+I t) d+r+3d/2-chi;
ZLVch2[{r_,d_,ch2_},{s_,t_}]:=-1/2 (s+I t)^2 r+ (s+I t) d-ch2;
Wall[{r_,d_,chi_},{rr_,dd_,cchi_},{s_,t_}]:=2 cchi (d-r s)-2 chi (dd-rr s)+(dd r-d rr) (2+3 s+s^2+t^2);
Wallch2[{r_,d_,ch2_},{rr_,dd_,cch2_},{s_,t_}]:=(s^2+t^2)(r dd-rr d)-2s (r cch2-rr ch2)+2(d cch2-dd ch2);


(* ::Section:: *)
(*Constructing Le Potier curve*)


ExcepSlopes=Range[-3,4];
Module[{mu1,mu2,Li},
Do[Li={};
Do[
mu1=ExcepSlopes[[i]];
mu2=ExcepSlopes[[i+1]];
AppendTo[Li,mu1];
AppendTo[Li,(mu1+mu2)/2+1/2(1/Denominator[mu1]^2-1/Denominator[mu2]^2)/(3+mu1-mu2)];,
{i,Length[ExcepSlopes]-1}];
AppendTo[Li,Last[ExcepSlopes]];
ExcepSlopes=Li;
,{j,4}]];
ExcepToChi[mu_]:=Module[{r},r=Denominator[mu];r{1,mu,1/2mu(mu+3)+1/2+1/(2r^2)}];
LPCurve[mu_]:=Max[Table[If[Abs[mu-Floor[mu]-ExcepSlopes[[i]]]<3,1/2(mu-Floor[mu]-ExcepSlopes[[i]])^2-3/2Abs[mu-Floor[mu]-ExcepSlopes[[i]]]+1-1/2(1-1/Denominator[ExcepSlopes[[i]]]^2),0],{i,Length[ExcepSlopes]}]];


(* ::Section:: *)
(*Basic operations on trees and lists of trees*)


(*If there is no "Ch" we probably already have a charge vector {r,d,chi}. If we have anything that's not a list (typically linear combinations of Ch[m_] or Ch[m_][p_]) then just use repCh or repCh2 and hope for the best.*)
TreeCharge[arg : {r_, d_, chi_} /; FreeQ[arg, Ch]] := {r, d, chi};
TreeCharge[trees_List] := Total[TreeCharge /@ trees];
TreeCharge[arg : Except[_List]] := arg /. repCh;
TreeChargech2[arg : {r_, d_, chi_} /; FreeQ[arg, Ch]] := chitoch2[{r, d, chi}];
TreeChargech2[trees_List] := Total[TreeChargech2 /@ trees];
TreeChargech2[arg : Except[_List]] := arg /. repCh2;

TreeConstituents[Tree_]:=(* gives the flattened list of constituents of a tree *)
If[!ListQ[Tree]||Length[Tree]==3,{Tree},
Join[TreeConstituents[Tree[[1]]],TreeConstituents[Tree[[2]]]]
];

FlipTree[Tree_]:=If[!ListQ[Tree],Tree/.Ch[m_]:>-Ch[-m],If[Length[Tree]==3,{-Tree[[1]],Tree[[2]],-Tree[[3]]+3Tree[[2]]},{FlipTree[Tree[[2]]],FlipTree[Tree[[1]]]}]];

ShiftTree[Tree_,k_]:=Tree/.{Ch[m_]:>Ch[m+k],{r_Integer,d_Integer,chi_Integer}:>SpecFlow[{r,d,chi},k]};

TreeTop[Tree_]:=If[Length[Tree]==2,xytost[IntersectRays[TreeCharge[Tree[[1]]],TreeCharge[Tree[[2]]]/.repCh]],Print["Argument is not a tree"]];

ScattCheck[Tree_]:=(* Check consistency of single tree, returns {charge,{xf,yf}} if tree is consistent, otherwise {charge,{}}; ignore whether leaves have Delta=0 or not *)
Module[{S1,S2,TreeNum},
If[!ListQ[Tree]||Length[Tree]==3,
(* tree consists of a single node *)
TreeNum=Tree/.repCh;
{Tree/.repCh,{TreeNum[[2]]/TreeNum[[1]],-1/2(TreeNum[[2]]/TreeNum[[1]])^2}},
(* otherwise, check each of the two branches *)
S1=ScattCheck[Tree[[1]]];
S2=ScattCheck[Tree[[2]]];
If[Length[S1[[2]]]>0&&Length[S2[[2]]]>0,{S1[[1]]+S2[[1]],IntersectRays[S1[[1]]/.repCh,S2[[1]]/.repCh,S1[[2]],S2[[2]]]},
{S1[[1]]+S2[[1]],{}}]
]];

ScattSort[LiTree_]:= (* sort trees by decreasing radius *)
Reverse[Map[#[[2]]&,SortBy[Table[{xytost[ScattCheck[LiTree[[i]]][[2]]][[2]],LiTree[[i]]},{i,Length[LiTree]}],N[First[#]]&]]];




(* ::Section:: *)
(*Computing local scattering*)


xytost[{x_,y_}]:={x,Sqrt[x^2+2y]};
sttoxy[{s_,t_}]:={s,-1/2(s^2-t^2)};

IntersectRays[{r_,d_,chi_},{rr_,dd_,cchi_}]:=
(* returns (x,y) coordinate of intersection point of two rays, or {} if they are collinear *)
If[(r dd-rr d!=0) (*&&(r rr+d dd<=0)*),{(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr),(cchi d-chi dd+dd r-d rr)/(-dd r+d rr)},{}];

IntersectRays[{r_,d_,chi_},{rr_,dd_,cchi_},z_,zz_]:=
(* returns (x,y) coordinate of intersection point of two rays, or {} if they don't intersect *)
Module[{zi},If[(r dd-rr d!=0) ,zi={(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr),(cchi d-chi dd+dd r-d rr)/(-dd r+d rr)};
If[(zi-z) . {-r,d}>=0&&(zi-zz) . {-rr,dd}>=0,zi,{}]]];

IntersectRaysSt[{r_,d_,chi_},{rr_,dd_,cchi_},psi_]:=
(* returns (s,t) coordinate of intersection point of two rays, or {} if they are collinear *)
If[(r dd-rr d!=0) ,If[TestBranch[{r,d,chi},(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr)]&&TestBranch[{rr,dd,cchi},(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr)],{(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr)-1/2Sin[psi]/Abs[r dd-rr d]\[Sqrt](4 cchi^2 r^2+4 chi^2 rr^2+4 chi (2 dd+3 rr) (dd r-d rr)+(dd r-d rr)^2+4 cchi (-2 d dd r-3 dd r^2+2 d^2 rr-2 chi r rr+3 d r rr)),1/2Cos[psi] /Abs[r dd-rr d]\[Sqrt](4 cchi^2 r^2+4 chi^2 rr^2+4 chi (2 dd+3 rr) (dd r-d rr)+(dd r-d rr)^2+4 cchi (-2 d dd r-3 dd r^2+2 d^2 rr-2 chi r rr+3 d r rr))},{}]];

TestBranch[{r_,d_,chi_},s_]:=Module[{Di},
(* tests if (s,.) is on the branch with ImZ>0 *)
If[r==0,d>0,
Di=Max[Disc[{r,d,chi}],0];
(s<=d/r-Sqrt[2Di] &&r>0)||(s>=d/r+Sqrt[2Di] &&r<0)
]];

Rayt[{r_,d_,chi_},s_,psi_]:=(* t(s) for the ray Re[E^(-I psi) Z_gam]\[Equal]0 *)
Which[2 d^2-2 d r (3+4 s)+4 r (chi+r (-1+s^2))-2 (d^2+3 d r+2 r (-chi+r)) Cos[2 psi]<0,0,r>0,1/(2 r) (Sqrt[2 d^2-2 d r (3+4 s)+4 r (chi+r (-1+s^2))-2 (d^2+3 d r+2 r (-chi+r)) Cos[2 psi]] Sec[psi]-2 d Tan[psi]+2 r s Tan[psi]),r<0,-(1/(2 r))(Sqrt[2 d^2-2 d r (3+4 s)+4 r (chi+r (-1+s^2))-2 (d^2+3 d r+2 r (-chi+r)) Cos[2 psi]] Sec[psi]+2 d Tan[psi]-2 r s Tan[psi]),
r==0,(chi/d-3/2-s)/Tan[psi]];

Rays[{r_,d_,chi_},t_,psi_]:=(* s(t) for the ray Re[E^(-I psi) Z_gam]\[Equal]0 *)
   If[r!=0,d/r-t Tan[psi]-Sign[r]/Cos[psi]Sqrt[t^2+2Disc[{r,d,chi}]Cos[psi]^2],chi/d-r/2-3/2-t Tan[psi]];

Raysch2[{r_,d_,ch2_},t_,psi_]:=(* s(t) for the ray Re[E^(-I psi) Z_gam]\[Equal]0 *)
If[r!=0,d/r-t Tan[psi]-Sign[r]/Cos[psi]Sqrt[t^2+2Disch2[{r,d,ch2}]Cos[psi]^2],ch2/d-t Tan[psi]];

Raytau1ch2LV[{r_,d_,ch2_},tau2_,psi_]:=(* tau1(tau2) for the ray Re[E^(-I psi) Z_gam]\[Equal]0 *)
Module[{tau1,tau10},
tau10=d/r-tau2 Tan[psi]-Sign[r]/Cos[psi]Sqrt[tau2^2+2Disch2[{r,d,ch2}]Cos[psi]^2];
tau1/.FindRoot[Re[Exp[-I psi](-r EichlerTDLV[tau1+I tau2]+d EichlerTLV[tau1+I tau2]-ch2)],{tau1,tau10}]];

Raytau1ch2C[{r_,d_,ch2_},tau2_,psi_]:=(* tau1(tau2) for the ray Re[E^(-I psi) Z_gam]\[Equal]0 *)
Module[{tau1,Exacttau1},
If[Length[Initialtau1]=0,
Initialtau1=d/r-tau2 Tan[psi]-Sign[r]/Cos[psi]Sqrt[tau2^2+2Disch2[{r,d,ch2}]Cos[psi]^2]];
Exacttau1=tau1/.FindRoot[Re[Exp[-I psi](-r EichlerTDC[tau1+I tau2]+d EichlerTC[tau1+I tau2]-ch2)],{tau1,Initialtau1}];
Initialtau1=Exacttau1
];

IntersectExactRaysLV[{r_,d_,chi_},{rr_,dd_,cchi_},psi_]:=
(* returns (tau1,tau2) coordinate of intersection point of two rays, or {} if they are collinear *)Module[{tau1,tau2,tau10,tau20},If[(r dd-rr d!=0) ,If[TestBranch[{r,d,chi},(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr)]&&TestBranch[{rr,dd,cchi},(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr)],{tau10,tau20}={(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr)-1/2Sin[psi]/Abs[r dd-rr d]\[Sqrt](4 cchi^2 r^2+4 chi^2 rr^2+4 chi (2 dd+3 rr) (dd r-d rr)+(dd r-d rr)^2+4 cchi (-2 d dd r-3 dd r^2+2 d^2 rr-2 chi r rr+3 d r rr)),1/2Cos[psi] /Abs[r dd-rr d]\[Sqrt](4 cchi^2 r^2+4 chi^2 rr^2+4 chi (2 dd+3 rr) (dd r-d rr)+(dd r-d rr)^2+4 cchi (-2 d dd r-3 dd r^2+2 d^2 rr-2 chi r rr+3 d r rr))};
{tau1,tau2}/.FindRoot[{Re[Exp[-I psi](-r EichlerTDLV[tau1+I tau2]+d EichlerTLV[tau1+I tau2]-(chi-3/2d-r))],Re[Exp[-I psi](-rr EichlerTDLV[tau1+I tau2]+dd EichlerTLV[tau1+I tau2]-(cchi-3/2dd-rr))]},{tau1,tau10},{tau2,tau20}]
,{}]]];


(* ::Section:: *)
(*Constructing scattering trees*)


ListSubsetsAny=Module[{LiSub,LiSubHalf},
(* precompute all binary splits of Range[n] for n=2..10; used by ListStableTrees *)
Table[
LiSub=Drop[Subsets[Range[n],Floor[(n-1)/2]],1];
If[EvenQ[n],
LiSubHalf=Subsets[Range[n],{n/2}];
LiSub=Union[LiSub,Take[LiSubHalf,Length[LiSubHalf]/2]]];LiSub,{n,2,10}]];


ListStableTrees[LiCh_,{s0_,t0_}]:=
Module[{n,LiTree,LiCh1,LiCh2,gam1,gam2,s1,t1,LiStable1,LiStable2},
(* for a given list of k_i Ch[m_i], construct consistent stable trees *)
n=Length[LiCh];
(*Print["**",LiCh,", (s,t)=",{s0,t0}]; *)
If[n==1, LiTree=LiCh,
(* construct possible subsets, avoiding double counting *) 
LiTree={};
Do[
LiCh1=ListSubsetsAny[[n-1,i]]/.n_Integer:>LiCh[[n]];
LiCh2=Complement[Range[n],ListSubsetsAny[[n-1,i]]]/.n_Integer:>LiCh[[n]];
(*Print[LiCh1,",",LiCh2];*)
gam1=Plus@@(LiCh1/.repCh);
gam2=Plus@@(LiCh2/.repCh);
(* reorder according to slope *)
If[GenSlope[gam1]>GenSlope[gam2],{gam1,gam2}={gam2,gam1};{LiCh1,LiCh2}={LiCh2,LiCh1}];
If[Wall[gam1,gam2,{s0,t0}]DSZ[gam1,gam2]>0,
{s1,t1}=xytost[IntersectRays[gam1,gam2]];
(*Print[gam1,",",gam2,",",s1];*)
If[TestBranch[gam1,s1]&&TestBranch[gam2,s1],
(*Print[LiCh1,LiCh2,gam1,gam2,s1,t1]; *)
LiStable1=ListStableTrees[LiCh1,{s1,t1}];
LiStable2=ListStableTrees[LiCh2,{s1,t1}];
Do[
AppendTo[LiTree,{LiStable1[[j1]],LiStable2[[j2]]}],
{j1,Length[LiStable1]},{j2,Length[LiStable2]}];
]];,
{i,Length[ListSubsetsAny[[n-1]]]}];
];LiTree
];

ListStableTreesPerturb[LiCh_,{s0_,t0_}]:=Module[{LiChPert},
LiChPert=LiCh/.{Ch[m_]:>{1,m,1+1/2m(m+3)-RandomInteger[100000]/10000000}};
Round[ListStableTrees[LiChPert,{s0,t0}]]];

ListStablePlanarTrees[LiCh_]:=Module[{Li,LiTree,Tree},
(* for a given list of k_i Ch[m_i], construct consistent PLANAR trees *)
Li={};LiTree=Groupings[List@@LiCh,2];
Do[Tree=LiTree[[i]];
If[Length[ScattCheck[Tree][[2]]]>0,AppendTo[Li,Tree]],{i,Length[LiTree]}];
Li];

ScanConstituents[gam_,{m0min_,m0max_},{nmin_,nmax_},phimax_]:=
(* searches possible list of constituents  with slope in [m0min,m0max], number of constituents in [nmin,nmax] and charges adding up to gam, *)
Module[{Li={},nc=0,Tabm0,Lim,Lik,Likp,k,kp,ktot,m,mp,m0,m0p},
(* look for possible set of constituents with total charge gam, slopes from m0min to m0max, number of constituents from nmin to nmax, and phi:=d-r s \[LessEqual]phimax *)
Tabm0=Select[Flatten[Table[If[m0-m0p<=phimax,{m0p,m0},{}],
{m0p,Floor[m0min],Ceiling[m0max]},{m0,m0p+1,Ceiling[m0max]}],1],Length[#]>0&];
Print["Possible values of {mmin,mmax}:", Tabm0];
Monitor[Do[(* loop on kk *)
{m0p,m0}=Tabm0[[kk]];
m[0]=m0;
mp[0]=m0p;
Do[(* loop on n,np *)
If[(n+np>=nmin)&&(n+np<=nmax),
(*PrintTemporary["Trying with ",np," left-movers and ", n," rightmovers"];*) 
Lim=Union [Table[{m[i],m0p,m[i-1]},{i,n-1}],Table[{mp[j],mp[j-1],m0},{j,np-1}]];
Do[(* loop on m *)
Lik=Table[{k[i],If[i>0,If[m[i]==m[i-1],k[i-1],1],1],2(phimax-m0+m0p+1)-Sum[k[ii],{ii,0,i-1}]},{i,0,n-1}];
  Do[ (* loop on k*)
ktot=Sum[k[ii],{ii,0,n-1}];
If[ktot<2phimax,
Likp=Table[{kp[j],If[j>0,If[mp[j]==mp[j-1],kp[j-1],1],1],2(phimax-m0+m0p+1)-ktot-Sum[kp[jj],{jj,0,j-1}]},{j,0,np-1}];
Do[(* loop on kp *)
nc+=1;
If[Sum[k[i]Ch[m[i]]/.repCh,{i,0,n-1}]-Sum[kp[j]Ch[mp[j]]/.repCh,{j,0,np-1}]==gam,AppendTo[Li,Join[Table[k[i]Ch[m[i]],{i,0,n-1}],Table[-kp[j] Ch[mp[j]],{j,0,np-1}]]]],
##]&@@Likp],
##]&@@Lik,
##]&@@Lim],
{n,1,nmax},{np,1,nmax}],
{kk,Length[Tabm0]}] ,{Ch[m0p],Ch[m0]}
];
Print[Length[Li]," possible sets of constituents out of ",nc," trials"];
Li];

ScanAllTrees[{r_,d_,chi_},{s0_,t0_}]:=Module[{Li,LiAllowed,phimax},
phimax=d-r s0;
If[phimax<=0,Print["There are no trees at this point"];,
Li=ScanConstituents[{r,d,chi},{s0-t0,s0+t0},{1,2phimax},phimax];
ScattSort[DeleteDuplicatesBy[Flatten[Select[Table[ListStableTrees[Li[[i]],{s0,t0}],{i,Length[Li]}],Length[#]>0&],1],ScattGraph]]]]

ScanBinarySplits[{r_,d_,chi_},t_]:=Module[{r1,Li,phi,smin,smax,d1min,d1max,d2min,d2max,chirange,s},
Li={};
s=Rays[{r,d,chi},t,0];Print["Ray starting at ",{s,t}];
phi=d-r s;
Do[(* loop on r1 *)
If[Abs[r1]+Abs[r-r1]<=2phi&&r1<=r-r1,
Which[r==0,smin=chi/d-3/2;smax=chi/d-3/2,
r>0&&Disc[{r,d,chi}]>0,smin=s;smax=d/r-Sqrt[2Disc[{r,d,chi}]],
r>0&&Disc[{r,d,chi}]<=0;smin=s;smax=d/r,
r<0&&Disc[{r,d,chi}]>0,smin=d/r+Sqrt[2Disc[{r,d,chi}];smax=s],
r<0&&Disc[{r,d,chi}]<=0;smin=d/r;smax=s];
d1min=Ceiling[ 1/2+If[r1>=0,r1 smin,r1 smax]];d1max=d-If[r-r1>=0,(r-r1)smin,(r-r1)smax]- 1/2;
d2min=Ceiling[1/2+If[r-r1>=0,(r-r1) smin,(r-r1)smax]];
d2max=d-If[r1>=0,r1 smin,r1 smax]-1/2;
(*Print[{r1,r-r1},",",{smin,smax}," - d1:",{d1min,d1max}," ,d2:",{d2min,d2max}];*)
Do[(* loop on d1,d2 *)If[d1+d2==d&&(r1!=0 || d1!=0)&&(r-r1!=0 || d-d1!=0)&& (r1 d-r d1!=0),
If[r!=0,
chirange=If[(r1 d-r d1)/r>0,
{Ceiling[(chi r1-(r1 d-r d1)(smax+3/2))/r],Floor[(chi r1-(r1 d-r d1)(smin+3/2))/r]},{Ceiling[(chi r1-(r1 d-r d1)(smin+3/2))/r],Floor[(chi r1-(r1 d-r d1)(smax+3/2))/r]}],
chirange=If[r1>0,
{Ceiling[r1+3/2 d1+d1 smin-1/2r1 smin^2+r1/8 ],Floor[r1+3/2 d1+d1 smin-1/2r1 smin^2+1/2 r1 t^2]},
{Ceiling[r1+3/2 d1+d1 smin-1/2r1 smin^2+1/2 r1 t^2],Floor[r1+3/2 d1+d1 smin-1/2r1 smin^2+r1/8 ]}]
];
(*Print[{r1,d1,{smin,smax},chirange}]; *)
Do[(* loop on ch *)
If[DiscR[{r1,d1,ch}]>=0&&DiscR[{r-r1,d-d1,chi-ch}]>=0,
AppendTo[Li,{{r1,d1,ch},{r-r1,d-d1,chi-ch}}]],
{ch,chirange[[1]],chirange[[2]]}]
],
{d1,d1min,d1max},
{d2,d2min,d2max}];],
{r1,-2Floor[phi],2Floor[phi]}];Li];

ScanKroneckerSplits[{r_,d_,chi_}]:=Module[{k,kp,mmax,mmin,A,Li},
(* look for 2-body trees {-k' O(m'), k O(m) } *)
Li={};
If[r>0,
A=(-2chi+3d+2r+d^2/r)/r;
If[A==0,Print["A vanishes"]];
mmax=Ceiling[d/r]-1;
mmin=Floor[d/r-A/(d/r-mmax)];
(*Print[{mmin,mmax}];*)
Do[If[A==(d/r-m)(d/r-mp),
k=(d-mp r)/(m-mp);kp=(d-m r)/(m-mp);
If[IntegerQ[k]&&IntegerQ[kp]&&k>=1&&kp>=1,
AppendTo[Li,{{-kp  Ch[mp],k Ch[m]}}];
]],
{m,mmin+1,mmax},{mp,mmin,m-1}],
If[r<0,Li=-ScanKroneckerSplits[{-r,-d,-chi}],
(* r=0 *)
Li=Map[If[IntegerQ[chi/d-3/2+d/#/2],{-# Ch[chi/d-3/2-d/#/2],# Ch[chi/d-3/2+d/#/2]},{}]&,Divisors[d]];
]];
Select[Li,Length[#]>0&]];




(* ::Section:: *)
(*Computing the index*)


ScattIndex[TreeList_]:=Table[
(* compute index for each tree in the list; do not trust the result if internal lines have non-primitive charges *)
Simplify[Times@@ScattIndexInternal[TreeList[[i]]][[2]]],{i,Length[TreeList]}];

ScattIndexInternal[Tree_]:=Module[{S1,S2,g1,g2,kappa,Li},
(* compute {total charge, list of Kronecker indices associated to each vertex *)
If[!ListQ[Tree]||Length[Tree]==3,{Tree,{1}},
S1=ScattIndexInternal[Tree[[1]]]/.repCh;
S2=ScattIndexInternal[Tree[[2]]]/.repCh;
g1=GCD@@S1[[1]];g2=GCD@@S2[[1]];
kappa=3Abs[(S1[[1,1]]S2[[1,2]]-S1[[1,2]]S2[[1,1]])/g1/g2];
Li=Join[S1[[2]],S2[[2]]];
AppendTo[Li,Subscript[Kr, kappa][Min[g1,g2],Max[g1,g2]]];
If[GCD@@(S1[[1]]+S2[[1]])!=1,Print["Beware, non-primitive state"]];
{S1[[1]]+S2[[1]],Li}]];

EvaluateKronecker[f_]:=
f/.Subscript[Kr, kappa_][g1_,g2_]:>Simplify[P2HiggsBranchFormula[{{0,kappa},{-kappa,0}},{1/g1,-1/g2},{g1,g2}]];

BinaryTreeIndex[TreeList_]:=Table[
(* compute index for each tree in the list; do not trust the result if internal lines have non-primitive charges *)
Simplify[Times@@BinaryTreeIndexInternal[TreeList[[i]]][[2]]],{i,Length[TreeList]}];

BinaryTreeIndexInternal[Tree_]:=Module[{S1,S2,kappa,Li},
If[!ListQ[Tree]||Length[Tree]==3,{Tree,{1}},
S1=BinaryTreeIndexInternal[Tree[[1]]]/.repCh;
S2=BinaryTreeIndexInternal[Tree[[2]]]/.repCh;
kappa=3Abs[(S1[[1,1]]S2[[1,2]]-S1[[1,2]]S2[[1,1]])];
Li=Join[S1[[2]],S2[[2]]];
AppendTo[Li,(-1)^(kappa+1)(y^kappa-y^(-kappa))/(y-1/y)];
{S1[[1]]+S2[[1]],Li}]];

AbelianizedScatteringSequence[ScattSeq_]:=Module[{Constituents,Multip,PrimitiveConstitutents,PartitionTable,k},
Constituents=TreeConstituents[ScattSeq];
Multip=Abs[Constituents/.Ch[x_]:>1];
PrimitiveConstitutents=Constituents/Multip;
PartitionTable=Table[IntegerPartitions[Multip[[i]]],{i,Length[Multip]}];
Flatten[Table[Sort[Flatten[Table[PartitionTable[[j,k[j]]]PrimitiveConstitutents[[j]],{j,Length[Multip]}]]],##]&@@Table[{k[i],Length[PartitionTable[[i]]]},{i,Length[Multip]}],Length[Multip]-1]];

IndexFromAbelianizedSequences[LiAbelianized_,{s0_,t0_}]:=Module[{LiAttIndices,LiSymFactors,LiCharges,LiTrees,k},
LiAttIndices=Abs[LiAbelianized/.Ch[x_]:>1]/.k_Integer:>(y-1/y)/k/(y^k-1/y^k);
LiSymFactors=Map[Length[Permutations[#]]/Length[#]!&,LiAbelianized];
Table[
LiCharges=LiAbelianized[[k]];
LiTrees=ListStableTreesPerturb[LiCharges,{s0,t0}];
(*Print[LiTrees/.{r_Integer,d_Integer,chi_Integer}:>r Ch[d/r]]; *)
LiSymFactors[[k]] (Times@@LiAttIndices[[k]])BinaryTreeIndex[LiTrees](* (BinaryTreeIndex[LiTrees]/.Subscript[Kr, kappa_][g1_,g2_]:>(-1)^(kappa g1 g2+1)(y^(kappa g1 g2)-y^(-kappa g1 g2))/(y-1/y))*),
{k,Length[LiAbelianized]}]];

IndexFromSequences[LiScattSeq_,{s0_,t0_}]:=Module[{LiAbelianized},LiAbelianized=DeleteDuplicates[Flatten[Map[AbelianizedScatteringSequence,LiScattSeq],1]];
IndexFromAbelianizedSequences[LiAbelianized,{s0,t0}]
]


(* taken in part from CoulombHiggs.m package *) 
P2HiggsBranchFormula[Mat_,Cvec_,Nvec_]:=Module[{Cvec0},
  If[Max[Nvec]<0,Print["P2HiggsBranchFormula: The dimension vector must be positive !"]];
  If[Plus@@Nvec==0,Return[0]];
  If[Plus@@Nvec==1,Return[1]];
  Cvec0=Cvec-(Plus@@(Nvec Cvec))/(Plus@@Nvec);
DivisorSum[GCD@@Nvec,(y-1/y)/(y^#-1/y^#)/# MoebiusMu[#] P2RationalInvariant[Mat,Cvec0,Nvec/#,y^#]&]];
P2RationalInvariant[Mat_,Cvec_,Nvec_,y_]:=Module[{Li,gcd},
	gcd=GCD@@Nvec;
	Li=Flatten[Map[Permutations,P2ListAllPartitions[{gcd}]],1];
	Sum[
	   Product[P2StackInvariant[Mat,Cvec,Nvec Li[[i,j,1]]/gcd,y],{j,Length[Li[[i]]]}]/Length[Li[[i]]]/(y-1/y)^(Length[Li[[i]]]-1),
	{i,Length[Li]}]];

P2QDeformedFactorial[n_,y_]:=If[n<0,Print["P2QDeformedFactorial[n,y] is defined only for n>=0"],
		If[n==0,1,(y^(2n)-1)/(y^2-1)P2QDeformedFactorial[n-1,y]]];
		
P2StackInvariant[Mat_,Cvec_,Nvec_,y_]:=Module[{m,JKListAllPermutations,pa,Cvec0},
  m=Length[Nvec];
  If[Max[Nvec]<0,Print["P2StackInvariant: The dimension vector must be positive !"]];
  If[Plus@@Nvec==0,Return[0]];
  If[Plus@@Nvec==1,Return[1]];
  Cvec0=Cvec-(Plus@@(Nvec Cvec))/(Plus@@Nvec);
  pa=Flatten[Map[Permutations,P2ListAllPartitions[Nvec]],1];
    (-y)^( Sum[-Max[Mat[[k,l]],0]Nvec[[k]]Nvec[[l]],{k,m},{l,m}]-1+Plus@@ Nvec)
	   (y^2-1)^(1-Plus@@Nvec)
	Sum[If[(Length[pa[[i]]]==1) ||And@@Table[Sum[Cvec0[[k]] pa[[i,a,k]],{a,b},{k,m}]>0,{b,Length[pa[[i]]]-1}],
      (-1)^(Length[pa[[i]]]-1)
       y^(2 Sum[Max[ Mat[[l,k]],0] pa[[i,a,k]]pa[[i,b,l]],
    {a,1,Length[pa[[i]]]},{b,a,Length[pa[[i]]]},{k,m},{l,m}])/
    Product[P2QDeformedFactorial[pa[[i,j,k]],y] ,{j,1,Length[pa[[i]]]},{k,m}],0],{i,Length[pa]}]
];
	
P2ListAllPartitions[gam_]:=Module[{m,unit,Li},
If[Plus@@gam==1, {{gam}},
		m=Max[Select[Range[Length[gam]],gam[[#]]>0&]];
        unit=Table[If[i==m,1,0],{i,Length[gam]}];        
	    Li=P2ListAllPartitions[gam-unit];
        Union[Map[Sort,
        Union[Flatten[
				Table[Union[Flatten[{{Flatten[{Li[[i]],{unit}},1]},
					    Table[
						  Table[If[j==k,Li[[i,j]]+unit,Li[[i,j]]]
						  ,{j,Length[Li[[i]]]}]
	                    ,{k,Length[Li[[i]]]}]}
                      ,1]]
				,{i,Length[Li]}],1]]
         ,1]]
	]];

P2BinarySplits[Nvec_]:=Module[{Li,Li1,Nl},
If[Plus@@Nvec==1,Li1=Nvec,
Li=Drop[Drop[Flatten[Table[Table[Nl[i],{i,Length[Nvec]}],Evaluate[Sequence@@Table[{Nl[i],0,Nvec[[i]]},{i,Length[Nvec]}]]],Length[Nvec]-1],1],-1];
Li1=Take[Li,Ceiling[Length[Li]/2]];
Li1]];




(* ::Section:: *)
(*Plotting scattering trees*)


TreeHue[n_,i_]:=Blend[{Brown,Green},i/n];

(*TreeHue[n_,i_]:=Hue[.5+.5 i/n];*)

Module[{LiSlopes,LiHeights},
(* keep track of height of labels for each slope *)

InitialLabelPosition[m_]:=Module[{p},
p=Position[LiSlopes,m];
If[Length[p]==0,
AppendTo[LiSlopes,m];
AppendTo[LiHeights,0];{m,-.2},
LiHeights[[p[[1,1]]]]+=1;
{m,-.2-.28*LiHeights[[p[[1,1]]]]}]];

ScattDiag[TreeList_]:=Module[{T,TNum,Diagram,DiagramList},
(* Draws scattering diagram in (x,y) plane for each tree in Treelist *)
LiSlopes={};LiHeights={};
DiagramList=Table[
T=ScattDiagInternal[TreeList[[i]]];
TNum=T/.repCh;
Diagram={TreeHue[Length[TreeList],i]};
AppendTo[Diagram,T[[3]]];
AppendTo[Diagram,Arrow[{TNum[[2]],TNum[[2]]+{-TNum[[1,1]],TNum[[1,2]]}/GCD@@(TNum[[1]])}]];
AppendTo[Diagram,Text[TNum[[1]],TNum[[2]]+{-TNum[[1,1]],.2+TNum[[1,2]]}/GCD@@(TNum[[1]])]];Graphics[Diagram],{i,Length[TreeList]}];
DiagramList];


ScattDiagOverlay[TreeList_]:=Module[{T,TNum,Diagram},
(* Draw overlayed diagrams in (x,y) plane for a LIST of trees *)
Diagram={};LiSlopes={};LiHeights={};
Do[T=ScattDiagInternal[TreeList[[i]]];
TNum=T/.repCh;
AppendTo[Diagram,TreeHue[Length[TreeList],i]];
AppendTo[Diagram,T[[3]]];
AppendTo[Diagram,Arrow[{TNum[[2]],TNum[[2]]+{-TNum[[1,1]],TNum[[1,2]]}/GCD@@(TNum[[1]])}]];,
{i,Length[TreeList]}];
Graphics[Diagram]];

ScattDiagInternal[Tree_]:=Module[{S1,S2,TreeNum,z,Li},
(* constructs total charge, coordinate of root and list of line segments in (x,y) coordinates, {min(x), max(x)}; used by ScattDiag *) 
If[!ListQ[Tree]||Length[Tree]==3,
(* a single charge *)
TreeNum=Tree/.repCh;
If[Disc[TreeNum]==0,
{Tree,{TreeNum[[2]]/TreeNum[[1]],-1/2(TreeNum[[2]]/TreeNum[[1]])^2},
{Text[Tree/.repChO,InitialLabelPosition[TreeNum[[2]]/TreeNum[[1]]]+{0,-1/2(TreeNum[[2]]/TreeNum[[1]])^2}]},{TreeNum[[2]]/TreeNum[[1]],TreeNum[[2]]/TreeNum[[1]]}},
(* the charge is not an O(m) *)
Print["Illegal endpoint"]],
(* a pair of charges *)
S1=ScattDiagInternal[Tree[[1]]];
S2=ScattDiagInternal[Tree[[2]]];
z=IntersectRays[S1[[1]]/.repCh,S2[[1]]/.repCh,S1[[2]],S2[[2]]];
If[Length[z]==0,Print["Illegal tree"]];
Li=S1[[3]];AppendTo[Li,S2[[3]]];AppendTo[Li,Arrow[{S1[[2]],z}]];AppendTo[Li,Arrow[{S2[[2]],z}]];
{S1[[1]]+S2[[1]],z,Li,{Min[S1[[4,1]],S2[[4,1]]],Max[S1[[4,2]],S2[[4,2]]]}}]
];

ScattDiagInternalSt[Tree_]:=Module[{S1,S2,TreeNum,z,Li},
(* construct total charge, coordinate of root and list of line segments in (s,t) coordinates, {min(x), max(x)} *) 
If[!ListQ[Tree]||Length[Tree]==3,
TreeNum=Tree/.repCh;If[Disc[TreeNum]==0,{Tree,{TreeNum[[2]]/TreeNum[[1]],0},{Text[Tree/.repChO,InitialLabelPosition[TreeNum[[2]]/TreeNum[[1]]]]},{TreeNum[[2]]/TreeNum[[1]],TreeNum[[2]]/TreeNum[[1]]}},Print["Illegal endpoint"]],
S1=ScattDiagInternalSt[Tree[[1]]];
S2=ScattDiagInternalSt[Tree[[2]]];
z=IntersectRays[S1[[1]]/.repCh,S2[[1]]/.repCh];
If[Length[z]==0,Print["Illegal tree"],
Li=S1[[3]];AppendTo[Li,S2[[3]]];AppendTo[Li,Arrow[{S1[[2]],xytost[z]}]];AppendTo[Li,Arrow[{S2[[2]],xytost[z]}]];
{S1[[1]]+S2[[1]],xytost[z],Li,{Min[S1[[4,1]],S2[[4,1]]],Max[S1[[4,2]],S2[[4,2]]]}}]]];

(* an extension to include arbitrary psi and Ch[p/q] constituents *)
ScattDiag[TreeList_,psi_]:=Module[{T,TNum,Diagram,DiagramList},
(* Draws scattering diagram in (x,y) plane for each tree in Treelist *)
DiagramList=Table[
T=ScattDiagInternal[TreeList[[i]],psi];
TNum=T/.repCh;
Diagram={TreeHue[Length[TreeList],i]};
AppendTo[Diagram,T[[3]]];
AppendTo[Diagram,Arrow[{TNum[[2]],TNum[[2]]+{-TNum[[1,1]],TNum[[1,2]]}/GCD@@(TNum[[1]])}]];
AppendTo[Diagram,Text[TNum[[1]],TNum[[2]]+{-TNum[[1,1]],.2+TNum[[1,2]]}/GCD@@(TNum[[1]])]];Graphics[Diagram],{i,Length[TreeList]}];
DiagramList];

ScattDiagxy[TreeList_,psi_]:=Module[{T,TNum,Diagram,xmin,xmax},
(* Draws scattering diagram in (x,y) plane for each tree in Treelist *)
Diagram={};xmin={};xmax={};LiSlopes={};LiHeights={};
Do[
T=ScattDiagInternal[TreeList[[i]],psi];
TNum=T/.repCh;
xmin=Min[xmin,TNum[[4,1]]];
xmax=Max[xmax,TNum[[4,2]]];
AppendTo[Diagram,TreeHue[Length[TreeList],i]];
AppendTo[Diagram,T[[3]]];
AppendTo[Diagram,Arrow[{TNum[[2]],TNum[[2]]+{-TNum[[1,1]],TNum[[1,2]]}/GCD@@(TNum[[1]])}]];
AppendTo[Diagram,Text[TNum[[1]],TNum[[2]]+{-TNum[[1,1]],.2+TNum[[1,2]]}/GCD@@(TNum[[1]])]];,{i,Length[TreeList]}];
Show[{Graphics[Diagram],Plot[-1/2t^2,{t,xmin,xmax}],Graphics[{Red,PointSize[Large],
Point[Table[{m+ QuantumVolume Tan[psi],-1/2m^2-m QuantumVolume Tan[psi]},{m,Floor[xmin],xmax}]],
Blue,PointSize[Medium],Point[Table[{m-1/2- 2QuantumVolume Tan[psi],-1/2(m^2-m+1)+(2m-1) QuantumVolume Tan[psi]},{m,Floor[xmin],xmax}]],
Green,PointSize[Small],Point[Table[{m-1/2,-1/3-1/2m(m-1)},{m,Floor[xmin],xmax}]]}]}]
];


ScattDiagInternal[Tree_,psi_]:=Module[{S1,S2,TreeNum,z,Li,Treexy},
(* constructs total charge, coordinate of root and list of line segments in (x,y) coordinates, {min(x), max(x)}; used by ScattDiag *) 
If[!ListQ[Tree]||Length[Tree]==3,
(* a single charge *)
TreeNum=Tree/.repCh;Treexy=(Tree/. { m_Integer Ch[tau1 : _Integer | _Rational][homshift_] | m_Integer Ch[tau1 : _Integer | _Rational] | Ch[tau1 : _Integer | _Rational][homshift_] | Ch[tau1 : _Integer | _Rational]  :>  CPointxy[tau1,psi]});
(*Print[Tree,",",TreeNum,"->",Treexy];*)
{Tree,Treexy,{Text[Tree/.repChO,Treexy+{0,Last[InitialLabelPosition[Treexy[[2]]/Treexy[[1]]]]}]},{Treexy[[1]],Treexy[[1]]}},
(* a pair of charges *)
S1=ScattDiagInternal[Tree[[1]],psi];
S2=ScattDiagInternal[Tree[[2]],psi];
z=IntersectRays[S1[[1]]/.repCh,S2[[1]]/.repCh,S1[[2]],S2[[2]]];
If[Length[z]==0,Print["Illegal tree"]];
Li=S1[[3]];AppendTo[Li,S2[[3]]];AppendTo[Li,Arrow[{S1[[2]],z}]];AppendTo[Li,Arrow[{S2[[2]],z}]];
{S1[[1]]+S2[[1]],z,Li,{Min[S1[[4,1]],S2[[4,1]]],Max[S1[[4,2]],S2[[4,2]]]}}]
];

ScattDiagInternalSt[Tree_,psi_]:=Module[{S1,S2,TreeNum,z,Li},
(* construct total charge, coordinate of root and list of line segments in (s,t) coordinates, {min(x), max(x)} *) 
If[!ListQ[Tree]||Length[Tree]==3,
TreeNum=Tree/.repCh;If[Disc[TreeNum]==0,{Tree,{TreeNum[[2]]/TreeNum[[1]],0},{Text[Tree/.repChO,InitialLabelPosition[TreeNum[[2]]/TreeNum[[1]]]]},{TreeNum[[2]]/TreeNum[[1]],TreeNum[[2]]/TreeNum[[1]]}},Print["Illegal endpoint"]],
S1=ScattDiagInternalSt[Tree[[1]],psi];
S2=ScattDiagInternalSt[Tree[[2]],psi];
z=IntersectRaysSt[S1[[1]]/.repCh,S2[[1]]/.repCh,psi];
If[Length[z]==0,Print["Illegal tree"],
Li=S1[[3]];AppendTo[Li,S2[[3]]];AppendTo[Li,Arrow[{S1[[2]],z}]];AppendTo[Li,Arrow[{S2[[2]],z}]];
{S1[[1]]+S2[[1]],z,Li,{Min[S1[[4,1]],S2[[4,1]]],Max[S1[[4,2]],S2[[4,2]]]}}]]];

ScattDiagSt[TreeList_,psi_]:=Module[{T,TNum,Diagram,xmin,xmax},
(* Draw overlayed diagrams in (s,t) plane for a LIST of trees *)
Diagram={};xmin={};xmax={};LiSlopes={};LiHeights={};
Do[T=ScattDiagInternalSt[TreeList[[i]],psi];
TNum=T/.repCh;
AppendTo[Diagram,TreeHue[Length[TreeList],i]];
AppendTo[Diagram,Dashing[None]];
AppendTo[Diagram,TNum[[3]]];
AppendTo[Diagram,Dashed];
AppendTo[Diagram,WallCircle[Plus@@TreeConstituents[TreeList[[i,1]]]/.repCh,Plus@@TreeConstituents[TreeList[[i,2]]]/.repCh]];
xmin=Min[xmin,TNum[[4,1]]];
xmax=Max[xmax,TNum[[4,2]]];
(*AppendTo[Diagram,Arrow[{T[[2]],T[[2]]+{0,1.5}}]]*)
,{i,Length[TreeList]}];
(*AppendTo[Diagram,Text[T[[1]],T[[2]]+{0,1}]]*);
AppendTo[Diagram,Dotted];
AppendTo[Diagram,Black];
(* AppendTo[Diagram,Table[{Line[{{k,0},{k+1/2,1/2},{k,1},{k-1/2,1/2},{k,0}}]},{k,-1+0Floor[xmin],-1+0Ceiling[xmax]}]];*)
Graphics[Diagram]];

ScattDiagSt[TreeList_]:=Module[{T,TNum,Diagram,xmin,xmax},
(* Draw overlayed diagrams in (s,t) plane for a LIST of trees *)
Diagram={};xmin={};xmax={};LiSlopes={};LiHeights={};
Do[T=ScattDiagInternalSt[TreeList[[i]]];
TNum=T/.repCh;
AppendTo[Diagram,TreeHue[Length[TreeList],i]];
AppendTo[Diagram,Dashing[None]];
AppendTo[Diagram,TNum[[3]]];
AppendTo[Diagram,Dashed];
AppendTo[Diagram,Circle[{TNum[[2,1]],0},TNum[[2,2]],{0,Pi}]];
xmin=Min[xmin,TNum[[4,1]]];
xmax=Max[xmax,TNum[[4,2]]];
(*AppendTo[Diagram,Arrow[{T[[2]],T[[2]]+{0,1.5}}]]*)
,{i,Length[TreeList]}];
(*AppendTo[Diagram,Text[T[[1]],T[[2]]+{0,1}]]*);
AppendTo[Diagram,Dotted];
AppendTo[Diagram,Black];
(* AppendTo[Diagram,Table[{Line[{{k,0},{k+1/2,1/2},{k,1},{k-1/2,1/2},{k,0}}]},{k,-1+0Floor[xmin],-1+0Ceiling[xmax]}]]; *)
Graphics[Diagram]];

ScattDiagInternalLV[Tree_,psi_,Styl_]:=Module[{S1,S2,TreeNum,z,Li},
(* construct total charge, coordinate of root and list of line segments in (s,t) coordinates, {min(x), max(x)} *) 
If[!ListQ[Tree]||Length[Tree]==3,
TreeNum=Tree/.repCh;If[Disc[TreeNum]==0,{Tree,{TreeNum[[2]]/TreeNum[[1]],0},
{Text[Tree/.repChO,InitialLabelPosition[TreeNum[[2]]/TreeNum[[1]]]]},{TreeNum[[2]]/TreeNum[[1]],TreeNum[[2]]/TreeNum[[1]]}},Print["Illegal endpoint"]],
S1=ScattDiagInternalLV[Tree[[1]],psi,Styl];
S2=ScattDiagInternalLV[Tree[[2]],psi,Styl];
z=IntersectRaysSt[S1[[1]]/.repCh,S2[[1]]/.repCh,psi];
If[Length[z]==0,Print["Illegal tree"],
Li=S1[[3]];AppendTo[Li,S2[[3]]];
AppendTo[Li,If[(S1[[1]]/.repCh)[[1]]==0||S1[[2,2]]==z[[2]],Line[{S1[[2]],z}],ParametricPlot[{Rays[S1[[1]]/.repCh,t,psi],t},{t,S1[[2,2]],z[[2]]},PlotStyle->Styl][[1]]]];
AppendTo[Li,If[(S2[[1]]/.repCh)[[1]]==0||S2[[2,2]]==z[[2]],Line[{S2[[2]],z}],ParametricPlot[{Rays[S2[[1]]/.repCh,t,psi],t},{t,S2[[2,2]],z[[2]]},PlotStyle->Styl][[1]]]];
{S1[[1]]+S2[[1]],z,Li,{Min[S1[[4,1]],S2[[4,1]]],Max[S1[[4,2]],S2[[4,2]]]}}]]];

ScattDiagLV[TreeList_,psi_]:=Module[{T,TNum,Diagram,xmin,xmax},
(* Draw overlayed diagrams in (s,t) plane for a LIST of trees *)
LiSlopes={};LiHeights={};
Diagram={AbsoluteThickness[1]};xmin={};xmax={};
Do[T=ScattDiagInternalLV[TreeList[[i]],psi,{TreeHue[Length[TreeList],i],AbsoluteThickness[1]}];
TNum=T/.repCh;
AppendTo[Diagram,TreeHue[Length[TreeList],i]];
AppendTo[Diagram,Dashing[None]];
AppendTo[Diagram,TNum[[3]]];
AppendTo[Diagram,Dashed];
AppendTo[Diagram,WallCircle[Plus@@TreeConstituents[TreeList[[i,1]]]/.repCh,Plus@@TreeConstituents[TreeList[[i,2]]]/.repCh]];
xmin=Min[xmin,TNum[[4,1]]];
xmax=Min[xmax,TNum[[4,2]]];AppendTo[Diagram,Dashing[None]];AppendTo[Diagram,Black];
AppendTo[Diagram,
If[(T[[1]]/.repCh)[[1]]==0, 
  Line[{T[[2]],T[[2]]+1.5{-Tan[psi],1}}],
  ParametricPlot[{Rays[T[[1]]/.repCh,t,psi],t},{t,T[[2,2]],T[[2,2]]+2},PlotStyle->{Black,AbsoluteThickness[1]}][[1]]]]
,{i,Length[TreeList]}];
AppendTo[Diagram,Dotted];
AppendTo[Diagram,Black];
Graphics[Diagram]];

ScattPhi[TreeList_]:=Module[{T,Diagram,DiagramList,phi},
(* Draw overlayed diagram in (s,phi) plane for each tree in the list *) 
Diagram={};LiSlopes={};LiHeights={};
Do[
T=ScattPhiInternal[TreeList[[i]]];
phi=T[[1,2]]-T[[1,1]]T[[2,1]];
AppendTo[Diagram,TreeHue[Length[TreeList],i]];
AppendTo[Diagram,Dashing[None]];
AppendTo[Diagram,T[[3]]];
T=T/.repCh;
AppendTo[Diagram,Text[phi,{T[[2,1]],phi+.1}]];
AppendTo[Diagram,Circle[{T[[2,1]],phi},.01]];
AppendTo[Diagram,Dotted];
AppendTo[Diagram,Line[{{T[[2,1]],phi},{T[[2,1]]-phi/2,0}}]];
AppendTo[Diagram,Line[{{T[[2,1]],phi},{T[[2,1]]+phi/2,0}}]];
(*AppendTo[Diagram,Line[{{T[[2,1]],phi},{T[[4,1]],0}}]];
AppendTo[Diagram,Line[{{T[[2,1]],phi},{T[[4,2]],0}}]]; *)
(* AppendTo[Diagram,Arrow[{T[[2]],T[[2]]+{0,1.5}}]];
AppendTo[Diagram,Text[T[[1]],T[[2]]+{0,1}]]; *),{i,Length[TreeList]}];
Graphics[Diagram]];

ScattPhiInternal[Tree_]:=Module[{S1,S2,TreeNum,z,Li},
(* compute {total charge, root coordinate, list of line segments in s,phi coordinates, {min(x), max(x)} *)
If[!ListQ[Tree]||Length[Tree]==3,
TreeNum=Tree/.repCh;If[Disc[TreeNum]==0,{TreeNum,{TreeNum[[2]]/TreeNum[[1]],-1/2(TreeNum[[2]]/TreeNum[[1]])^2},{Text[Tree/.repChO,
  InitialLabelPosition[TreeNum[[2]]/TreeNum[[1]]]]},{TreeNum[[2]]/TreeNum[[1]],TreeNum[[2]]/TreeNum[[1]]}},Print["Illegal endpoint"]],
S1=ScattPhiInternal[Tree[[1]]];
S2=ScattPhiInternal[Tree[[2]]];
z=IntersectRays[S1[[1]]/.repCh,S2[[1]]/.repCh,S1[[2]],S2[[2]]];
If[Length[z]==0,Print["Illegal tree"],
Li=S1[[3]];AppendTo[Li,S2[[3]]];
AppendTo[Li,Text[S1[[1,2]]-S1[[1,1]]z[[1]],{z[[1]]-.05,S1[[1,2]]-S1[[1,1]]z[[1]]}]];
AppendTo[Li,Text[S2[[1,2]]-S2[[1,1]]z[[1]],{z[[1]]+.05,S2[[1,2]]-S2[[1,1]]z[[1]]}]];
AppendTo[Li,Line[{{S1[[2,1]],S1[[1,2]]-S1[[1,1]]S1[[2,1]]},{z[[1]],S1[[1,2]]-S1[[1,1]]z[[1]]}}]];AppendTo[Li,Line[{{S2[[2,1]],S2[[1,2]]-S2[[1,1]]S2[[2,1]]},{z[[1]],S2[[1,2]]-S2[[1,1]]z[[1]]}}]];
{S1[[1]]+S2[[1]],z,Li,{Min[S1[[4,1]],S2[[4,1]]],Max[S1[[4,2]],S2[[4,2]]]}}]]];

ScattGraph[Tree_]:=Module[{T,LiArrows,LiVertex},
(* extracts list of vertices and adjacency matrix *)
LiSlopes={};LiHeights={};
T=ScattDiagInternal[Tree];
LiArrows=Cases[Flatten[T[[3]]],x_Arrow]/.Arrow[x_]:>x;
LiVertex=Union[Flatten[LiArrows,1]];
{LiVertex,Table[If[i!=j,Sign[Count[LiArrows,{LiVertex[[i]],LiVertex[[j]]}]],0],{i,Length[LiVertex]},{j,Length[LiVertex]}]}];

];


xytosq[{x_,y_}]:={x,y+x^2};
ScattDiagLZ[TreeList_]:=Module[{T,TNum,Diagram,xmin,xmax},
(* Draw over diagram in Li-Zhao coordinates (s,q=y+s^2) plane for each tree in the list *)
Diagram={};xmin={};xmax={};Do[
T=ScattDiagInternal[TreeList[[i]]]/.{Text[t_,{x_,y_}]:>Text[t,{x+.5Sign[x],1/2x^2}],Arrow[{{x1_,y1_},{x2_,y2_}}]:>Arrow[{xytosq[{x1,y1}],xytosq[{x2,y2}]}]};
TNum=T/.repCh;
AppendTo[Diagram,TreeHue[Length[TreeList],i]];
AppendTo[Diagram,T[[3]]];
AppendTo[Diagram,Dashed];
AppendTo[Diagram,WallLine[Plus@@TreeConstituents[TreeList[[i,1]]]/.repCh,Plus@@TreeConstituents[TreeList[[i,2]]]/.repCh]];
xmin=Min[xmin,TNum[[4,1]]];
xmax=Min[xmax,TNum[[4,2]]];
(*AppendTo[Diagram,Arrow[{TNum[[2]],TNum[[2]]+{-TNum[[1,1]],TNum[[1,2]]}/GCD@@(TNum[[1]])}]];
AppendTo[Diagram,Text[TNum[[1]],TNum[[2]]+{-TNum[[1,1]],.2+TNum[[1,2]]}/GCD@@(TNum[[1]])]];*)
,{i,Length[TreeList]}];Show[Graphics[Diagram],Plot[1/2x^2,{x,xmin-.2,xmax+.2}]]];
WallLine[{r_,d_,chi_},{rr_,dd_,cchi_}]:=Module[{s1,s2},
(* wall in Li-Zhao coordinates *)
s1=1/(2 dd r-2 d rr) (2 cchi r-3 dd r-2 chi rr+3 d rr+2 Sqrt[2 (dd r-d rr) (-cchi d+chi dd-dd r+d rr)+1/4 (2 cchi r-3 dd r-2 chi rr+3 d rr)^2]);
s2=1/(2 dd r-2 d rr) (2 cchi r-3 dd r-2 chi rr+3 d rr-2 Sqrt[2 (dd r-d rr) (-cchi d+chi dd-dd r+d rr)+1/4 (2 cchi r-3 dd r-2 chi rr+3 d rr)^2]);
Line[{{s1,1/2s1^2},{s2,1/2 s2^2}}]];


PlotWallRay[{r_,d_,chi_},{rr_,dd_,cchi_},psi_,{L1_,L2_,H_}]:=Module[{R,ch2,cch2,x,xx,Di,Ddi,s},
ch2=chi-r-3/2d;
cch2=cchi-rr-3/2dd;
x=0;xx=0;
If[r!=0,Di=Disc[{r,d,chi}];x=If[Di>=0,Cos[psi]Sqrt[2Di],0]];
If[rr!=0,Ddi=Disc[{rr,dd,cchi}];xx=If[Ddi>=0,Cos[psi] Sqrt[2Ddi],0]];
R=((r cch2-rr ch2)/(r dd-rr d))^2-2(d cch2-dd ch2)/(r dd-rr d);
(*Print[{Di,Ddi,R,x,xx}];*)
Show[Flatten[{
If[r!=0,
{Plot[Rayt[{r,d,chi},s,psi],{s,L1,d/r-x },
PlotStyle->{Red,If[r>0,Thick,Dashed]}],
Plot[Rayt[{r,d,chi},s,psi],{s,d/r+x,L2},
PlotStyle->{Red,If[r<0,Thick,Dashed]}]},
Graphics[{Red,If[d>0,Thick,Dashed],Line[{{chi/d-3/2,0},{chi/d-3/2-H Tan[psi],H}}]}]],
If[rr!=0,
{Plot[Rayt[{rr,dd,cchi},s,psi],{s,L1,dd/rr-xx},
PlotStyle->{Blue,If[rr>0,Thick,Dashed]}],
Plot[Rayt[{rr,dd,cchi},s,psi],{s,dd/rr+xx,L2},
PlotStyle->{Blue,If[rr<0,Thick,Dashed]}]},
Graphics[{Blue,If[dd>0,Thick,Dashed],Line[{{cchi/dd-3/2,0},{cchi/dd-3/2-H Tan[psi],H}}]}]],
If[r dd-rr d==0,Print["Charge vectors are collinear !"];Graphics[{Dotted,Line[{{d/r,0},{d/r,1}}]}],
If[R<0,Print["Radius is imaginary!"];{},
Plot[Sqrt[R-(s-(r cch2-rr ch2)/(r dd-rr d))^2],{s,(r cch2-rr ch2)/(r dd-rr d)-Sqrt[R],(r cch2-rr ch2)/(r dd-rr d)+Sqrt[R]},PlotStyle->{Black,Dotted}]]]}],
PlotRange->{{L1,L2},{0,H}},AxesOrigin->{0,0}]];

WallCircle[{r_,d_,chi_},{rr_,dd_,cchi_}]:=Circle[{(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr),0},Sqrt[((2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr))^2-2(d (cchi-rr-3/2dd)-dd (chi-r-3d/2))/(r dd-rr d)],{0,Pi}];



(* ::Section:: *)
(*Routines for McKay scattering diagram*)


chiton[{r_,d_,chi_}]:={-chi,r+d-chi,r+2d-chi};
ntochi[{n1_,n2_,n3_}]:={2n2-n1-n3,n3-n2,-n1};
repChn={Ch[m_]:>chiton[{1,m,1+m (m+3)/2}]};
DimMcKay[{n1_,n2_,n3_}]:=Max[3n1 n2+3 n2 n3-3 n3 n1,3n1 n2-3 n2 n3+3 n3 n1,-3n1 n2+3 n2 n3+3 n3 n1]-n1^2-n2^2-n3^2+1;
McKayDSZ[{n1_,n2_,n3_},{nn1_,nn2_,nn3_}]:=3 (n3 (nn1-nn2)+n1 (nn2-nn3)+n2 (-nn1+nn3));
McKayVec[{n1_,n2_,n3_}]:=-{Sqrt[3](n1-n3),(-2 n2+n1+n3)};
McKayRay[{n1_,n2_,n3_},{u_,v_},{k1_,k2_},tx_]:=(* produces from {u,v}+k1 vec to (u,v)+k2 vec, decorated with text at the target *)
{Arrow[{{u,v}+k1 McKayVec[{n1,n2,n3}],{u,v}+k2 McKayVec[{n1,n2,n3}]}],Text[tx,{u,v}+(k2+.1) McKayVec[{n1,n2,n3}]]};
McKayrep={n1_,n2_,n3_}:>n1 Subscript[\[Gamma], 1]+n2  Subscript[\[Gamma], 2 ]+n3 Subscript[\[Gamma], 3 ];
McKayRayEq[{n1_,n2_,n3_},{u_,v_}]:=n1+n2+n3+Sqrt[3] n1 v-Sqrt[3] n3 v-(-2 n2+n1+n3) u;
McKayIntersectRays[{n1_,n2_,n3_},{nn1_,nn2_,nn3_}]:=If[(n3 (nn1-nn2)+n1 (nn2-nn3)+n2 (-nn1+nn3))!=0,{(n3 (2 nn1+nn2)+n2 (nn1-nn3)-n1 (nn2+2 nn3))/(2 (n3 (nn1-nn2)+n1 (nn2-nn3)+n2 (-nn1+nn3))),(Sqrt[3] ((n1+n3) nn2-n2 (nn1+nn3)))/(2 (n3 (-nn1+nn2)+n2 (nn1-nn3)+n1 (-nn2+nn3)))},{}];
McKayIntersectRays[{n1_,n2_,n3_},{nn1_,nn2_,nn3_},z_,zz_]:=
(* returns (x,y) coordinate of intersection point of two rays, or {} if they don't intersect *)
Module[{zi},If[(n3 (nn1-nn2)+n1 (nn2-nn3)+n2 (-nn1+nn3)!=0) ,zi={(n3 (2 nn1+nn2)+n2 (nn1-nn3)-n1 (nn2+2 nn3))/(2 (n3 (nn1-nn2)+n1 (nn2-nn3)+n2 (-nn1+nn3))),(Sqrt[3] ((n1+n3) nn2-n2 (nn1+nn3)))/(2 (n3 (-nn1+nn2)+n2 (nn1-nn3)+n1 (-nn2+nn3)))};
If[(zi-z) . McKayVec[{n1,n2,n3}]>=0&&(zi-zz) . McKayVec[{nn1,nn2,nn3}]>=0,zi,{}]]];

McKayScattDiag[TreeList_]:=Module[{T,TNum,Diagram},
(* Draws scattering diagram in (x,y) plane for each tree in Treelist *)
Diagram={};Do[
T=McKayScattDiagInternal[TreeList[[i]]];
TNum=T/.repChn;
AppendTo[Diagram,TreeHue[Length[TreeList],i]];
AppendTo[Diagram,T[[3]]];
AppendTo[Diagram,Arrow[{TNum[[2]],TNum[[2]]+McKayVec[TNum[[1]]]/GCD@@(TNum[[1]])}]];
AppendTo[Diagram,Text[TNum[[1]]/.McKayrep,TNum[[2]]+McKayVec[TNum[[1]]]/GCD@@(TNum[[1]])]];
,{i,Length[TreeList]}];
Graphics[Diagram]];

McKayScattDiagInternal[Tree_]:=Module[{S1,S2,TreeNum,z,Li},
(* construct total charge, coordinate of root and list of line segments in (x,y) coordinates *) 
If[!ListQ[Tree]||Length[Tree]==3,
(* initial ray *)
TreeNum=Tree/.repChn;
z={};
Which[
TreeNum[[1]]>=1&&TreeNum[[2]]==0 && TreeNum[[3]]==0 ,z={1,0}-2McKayVec[{1,0,0}],
TreeNum[[2]]>=1&&TreeNum[[3]]==0 && TreeNum[[1]]==0 ,z={-1/2,-Sqrt[3]/2}-2McKayVec[{0,1,0}],
TreeNum[[3]]>=1&&TreeNum[[1]]==0 && TreeNum[[2]]==0 ,z={-1/2,Sqrt[3]/2}-2 McKayVec[{0,0,1}]];
If[z=={},Print["Illegal endpoint"],{Tree,z,{Text[Tree/.repChO/.McKayrep,z-.2 McKayVec[TreeNum]]}}],
(* non-trivial tree *)
S1=McKayScattDiagInternal[Tree[[1]]];
S2=McKayScattDiagInternal[Tree[[2]]];
z=McKayIntersectRays[S1[[1]]/.repChn,S2[[1]]/.repChn];
If[Length[z]==0,Print["Illegal tree"],
Li=S1[[3]];AppendTo[Li,S2[[3]]];AppendTo[Li,Arrow[{S1[[2]],z}]];AppendTo[Li,Arrow[{S2[[2]],z}]];
{S1[[1]]+S2[[1]],z,Li}]]];

(* No labels:
McKayScattDiagInternal[Tree_]:=Module[{S1,S2,TreeNum,z,Li},
(* construct total charge, coordinate of root and list of line segments in (x,y) coordinates *) 
If[!ListQ[Tree]||Length[Tree]==3,
(* initial ray *)
TreeNum=Tree/.repChn;
z={};
Which[
TreeNum[[1]]>=1&&TreeNum[[2]]==0 && TreeNum[[3]]==0 ,z={1,0}-2.5 McKayVec[{1,0,0}],
TreeNum[[2]]>=1&&TreeNum[[3]]==0 && TreeNum[[1]]==0 ,z={-1/2,-Sqrt[3]/2}-2.5 McKayVec[{0,1,0}],
TreeNum[[3]]>=1&&TreeNum[[1]]==0 && TreeNum[[2]]==0 ,z={-1/2,Sqrt[3]/2}-2.5 McKayVec[{0,0,1}]];
If[z=={},Print["Illegal endpoint"],{Tree,z,{}}],
(* non-trivial tree *)
S1=McKayScattDiagInternal[Tree[[1]]];
S2=McKayScattDiagInternal[Tree[[2]]];
z=McKayIntersectRays[S1[[1]]/.repChn,S2[[1]]/.repChn];
If[Length[z]==0,Print["Illegal tree"],
Li=S1[[3]];AppendTo[Li,S2[[3]]];AppendTo[Li,Arrow[{S1[[2]],z}]];AppendTo[Li,Arrow[{S2[[2]],z}]];
{S1[[1]]+S2[[1]],z,Li}]]];*)

McKayScattCheck[Tree_]:=(* Check consistency of single tree, returns {charge,{xf,yf}} if tree is consistent, otherwise {charge,{}} *)
Module[{S1,S2,TreeNum,z},
If[!ListQ[Tree]||Length[Tree]==3,
(* tree consists of a single node *)
TreeNum=Tree/.repChn;
z={};
Which[
TreeNum[[1]]>=1&&TreeNum[[2]]==0 && TreeNum[[3]]==0 ,z={1,0}-10 McKayVec[{1,0,0}],
TreeNum[[2]]>=1&&TreeNum[[3]]==0 && TreeNum[[1]]==0 ,z={-1/2,-Sqrt[3]/2}-10 McKayVec[{0,1,0}],
TreeNum[[3]]>=1&&TreeNum[[1]]==0 && TreeNum[[2]]==0 ,z={-1/2,Sqrt[3]/2}-10 McKayVec[{0,0,1}],
True,z=-10 McKayVec[TreeNum]];
{Tree/.repChn,z},
(* otherwise, check each of the two branches *)
S1=McKayScattCheck[Tree[[1]]];
S2=McKayScattCheck[Tree[[2]]];
If[Length[S1[[2]]]>0&&Length[S2[[2]]]>0,{S1[[1]]+S2[[1]],McKayIntersectRays[S1[[1]]/.repChn,S2[[1]]/.repChn,S1[[2]],S2[[2]]]},
{S1[[1]]+S2[[1]],{}}]
]];

McKayScattIndex[TreeList_]:=Table[
(* compute index for each tree in the list; do not trust the result if internal lines have non-primitive charges *)
Simplify[Times@@McKayScattIndexInternal[TreeList[[i]]][[2]]],{i,Length[TreeList]}];

McKayScattIndexInternal[Tree_]:=Module[{S1,S2,g1,g2,kappa,Li},
(* compute {total charge, list of Kronecker indices associated to each vertex *)
If[!ListQ[Tree]||Length[Tree]==3,{Tree,{1}},
S1=McKayScattIndexInternal[Tree[[1]]]/.repCh;
S2=McKayScattIndexInternal[Tree[[2]]]/.repCh;
g1=GCD@@S1[[1]];g2=GCD@@S2[[1]];
kappa=Abs[McKayDSZ[S1[[1]],S2[[1]]]]/g1/g2;
Li=Join[S1[[2]],S2[[2]]];
AppendTo[Li,Subscript[Kr, kappa][Min[g1,g2],Max[g1,g2]]];
If[GCD@@(S1[[1]]+S2[[1]])!=1,Print["Beware, non-primitive state"]];
{S1[[1]]+S2[[1]],Li}]];

McKayScattGraph[Tree_]:=Module[{T,LiArrows,LiVertex},
(* extracts list of vertices and adjacency matrix *)
T=McKayScattDiagInternal[Tree];
LiArrows=Cases[Flatten[T[[3]]],x_Arrow]/.Arrow[x_]:>x;
LiVertex=Union[Flatten[LiArrows,1]];
{LiVertex,Table[If[i!=j,Sign[Count[LiArrows,{LiVertex[[i]],LiVertex[[j]]}]],0],{i,Length[LiVertex]},{j,Length[LiVertex]}]}];

McKayListAllTrees[Nvec_]:=Module[{LiTrees,LiTree1,LiTree2,Li},
(* generate all trees with leaves carrying charge {p,0,0}, {0,p,0},{0,0,p} and with non-zero DSZ pairing at each vertex *)
LiTrees={};
If[Nvec[[1]]Nvec[[2]]==0&&Nvec[[2]]Nvec[[3]]==0&&Nvec[[3]]Nvec[[1]]==0,
LiTrees={Nvec};,
Li=Select[P2BinarySplits[Nvec],McKayDSZ[#,Nvec]!=0 &];
Do[
LiTree2=McKayListAllTrees[Li[[i]]];
LiTree1=McKayListAllTrees[Nvec-Li[[i]]];
Do[AppendTo[LiTrees,{LiTree1[[j]],LiTree2[[k]]}],{j,Length[LiTree1]},{k,Length[LiTree2]}];
,{i,Length[Li]}];
];LiTrees];

McKayScanAllTrees[Nvec_]:=Module[{Li,Li2},
(* generate consistent scattering trees with leaves carrying charge {p,0,0}, {0,p,0},{0,0,p}, with non-zero DSZ pairing at each vertex, with distinct support*)
Li=McKayListAllTrees[Nvec];
Li2=Select[Li,Length[McKayScattCheck[#][[2]]]>0&];
DeleteDuplicatesBy[ReverseSortBy[Li2,Length],McKayScattGraph]];

McKayInitialRays[psi_,L_]:=Module[{V},
V=QuantumVolume Tan[psi];
Show[Graphics[{
McKayRay[{1,0,0},{-1/2V+1/12,-1/(2Sqrt[3])(1/2+V)},L{0,1},"\!\(\*SubscriptBox[\(\[Gamma]\), \(1\)]\)"],
McKayRay[{0,1,0},{-1/6,V/Sqrt[3]},L{0,1},"\!\(\*SubscriptBox[\(\[Gamma]\), \(2\)]\)"],
McKayRay[{0,0,1},{1/2V+1/12,1/(2Sqrt[3])(1/2-V)},L{0,1},"\!\(\*SubscriptBox[\(\[Gamma]\), \(3\)]\)"],
Dashed,Line[2L{{-1,0},{1,0}}],Line[2L{{0,-1},{0,1}}],Dotted,
Line[{{-1/2V+1/12,-1/(2Sqrt[3])(1/2+V)},{-1/6,V/Sqrt[3]},{1/2V+1/12,1/(2Sqrt[3])(1/2-V)},{-1/2V+1/12,-1/(2Sqrt[3])(1/2+V)}}]}
],AspectRatio->1,PlotRange->{3{-1,1},3{-1,1}}]];

McKayInitialRays[L_]:=
Graphics[{McKayRay[{1,0,0},{1,0},L{-1.7,1.7},"\!\(\*SubscriptBox[\(\[Gamma]\), \(1\)]\)"],
McKayRay[{0,1,0},{-1/2,-Sqrt[3]/2},L{-1,1.4},"\!\(\*SubscriptBox[\(\[Gamma]\), \(2\)]\)"],
McKayRay[{0,0,1},{-1/2,Sqrt[3]/2},L{-1.3,1.6},"\!\(\*SubscriptBox[\(\[Gamma]\), \(3\)]\)"],Dashed,
Line[L{{-3,0},{5,0}}],Line[L{{0,-2.8},{0,3}}]}];



(* ::Section:: *)
(*Plotting fundamental domains of Gamma_1(3)*)


ToFundDomainC[{tau_,M_}]:=Module[{tau1,tau2},
(* produces {tau',M'} such that M'.tau'=M.tau and tau in fundamendal domain of Gamma_1(3) centered around conifold *)
{tau1,tau2}=ReIm[tau];If[tau2<=0,tau2=.000001];
Which[tau1<-1/2 || tau1>=1/2,ToFundDomainC[{tau-Floor[tau1+1/2],M . {{1,0,0},{Floor[tau1+1/2],1,0},{1/2Floor[tau1+1/2]^2,Floor[tau1+1/2],1}}}],
(tau1+1/3)^2+tau2^2<1/9,ToFundDomainC[{tau/(1+3 tau),M . {{1,0,0},{0,1,-3},{0,0,1}}}],
(tau1-1/3)^2+tau2^2<=1/9,ToFundDomainC[{tau/(1-3 tau),M . {{1,0,0},{0,1,3},{0,0,1}}}],
True,{tau,M}]];
ToFundDomainC[tau_]:=ToFundDomainC[{tau,IdentityMatrix[3]}];

ToFundDomainO[{tau_,m_}]:=Module[{tau1,tau2},
(* produces {tau',m'} such that m'.tau'=m.tau and tau in fundamendal domain of Gamma_0(3)centered around orbifold *)
{tau1,tau2}=ReIm[tau];If[tau2<=0,tau2=.000001];
Which[tau1<0 || tau1>=1,ToFundDomainO[{tau-Floor[tau1],m . {{1,0,0},{Floor[tau1],1,0},{1/2Floor[tau1]^2,Floor[tau1],1}}}],
(tau1-1/3)^2+tau2^2<1/9,ToFundDomainO[{(-1+2 tau)/(-1+3 tau),m . {{1,0,0},{1/2,-2,3},{1/2,-1,1}}}],
(tau1-2/3)^2+tau2^2<=1/9,ToFundDomainO[{(-1+tau)/(-2+3 tau),m . {{1,0,0},{1,1,-3},{1/2,1,-2}}}],
True,{tau,m}]];
ToFundDomainO[tau_]:=ToFundDomainO[{tau,IdentityMatrix[3]}];

Module[{tau1,tau2},
ToFundDomainCApprox[{tau_,M_},tolerance_:0.001]:=(
(* produces {tau',M'} such that M'.tau'=M.tau and tau is approximately in the fundamendal domain of Gamma_1(3) centered around the conifold *)
{tau1,tau2}=ReIm[tau];If[tau2<=0,tau2=.000001];
Which[tau1<-1/2 -tolerance|| tau1>=1/2+tolerance,ToFundDomainCApprox[{tau-Floor[tau1+1/2],M . {{1,0,0},{Floor[tau1+1/2],1,0},{1/2Floor[tau1+1/2]^2,Floor[tau1+1/2],1}}}],
(tau1+1/3)^2+tau2^2<1/9-tolerance,
ToFundDomainCApprox[{tau/(1+3 tau),M . {{1,0,0},{0,1,-3},{0,0,1}}}],
(tau1-1/3)^2+tau2^2<=1/9-tolerance,
ToFundDomainCApprox[{tau/(1-3 tau),M . {{1,0,0},{0,1,3},{0,0,1}}}],
True,
{tau,M}]);];
ToFundDomainCApprox[tau_]:=ToFundDomainCApprox[{tau,IdentityMatrix[3]}];

ToFundDomainCSeq[{tau_,M_}]:=Module[{tau1,tau2},
(* produces {tau'|,M} such that M'.tau'=M.tau and tau' in fundamendal domain of Gamma_1(3) centered around conifold, M represented as a sequence of U,V,T[m] transformations *)
{tau1,tau2}=ReIm[tau];If[tau2<=0,tau2=.000001];
Which[tau1<-1/2 || tau1>=1/2,ToFundDomainCSeq[{tau-Floor[tau1+1/2],M<>"T["<>ToString[Floor[tau1+1/2]]<>"]"}],
(tau1+1/3)^2+tau2^2<1/9,ToFundDomainCSeq[{tau/(1+3 tau),M<>"V"}],
(tau1-1/3)^2+tau2^2<=1/9,ToFundDomainCSeq[{tau/(1-3 tau),M<>"U"}],
True,{tau,M}]];

ToFundDomainCSeq[tau_]:=ToFundDomainCSeq[{tau,""}];


Module[{tau1,tau2},
ToFundDomainOApprox[{tau_,M_},tolerance_:0.001]:=(
(* produces {tau',M'} such that M'.tau'=M.tau and tau in fundamendal domain of Gamma_0(3)centered around orbifold *)
{tau1,tau2}=ReIm[tau];If[tau2<=0,tau2=tolerance];
Which[tau1<0-tolerance || tau1>=1+tolerance,ToFundDomainO[{tau-Floor[tau1],M . {{1,0,0},{Floor[tau1],1,0},{1/2Floor[tau1]^2,Floor[tau1],1}}}],
(tau1-1/3)^2+tau2^2<1/9-tolerance,ToFundDomainO[{(-1+2 tau)/(-1+3 tau),M . {{1,0,0},{1/2,-2,3},{1/2,-1,1}}}],
(tau1-2/3)^2+tau2^2<=1/9-tolerance,ToFundDomainO[{(-1+tau)/(-2+3 tau),M . {{1,0,0},{1,1,-3},{1/2,1,-2}}}],
True,{tau,M}])];
ToFundDomainOApprox[tau_]:=ToFundDomainOApprox[{tau,IdentityMatrix[3]}];


ApplyGamma13Lift[M_,tau_]:=If[Det[M]!=1 ||M[[1,2]]!=0||M[[1,3]]!=0 || Mod[M[[2,3]],3]!=0,Print["This is not a lifted element of Gamma_1(3)"],(M[[3,3]]tau+M[[3,2]])/(M[[2,3]]tau+M [[2,2]])];

MonodromyOnCharge[M_,{r_,d_,chi_}]:=If[Length[M]==0,{r,d,chi},If[
Depth[M]==3,
(* a single matrix *)
ch2tochi[{r,d,chi-r-3/2d} . {{0,0,-1},{0,1,0},{-1,0,0}} . Inverse[M] . {{0,0,-1},{0,1,0},{-1,0,0}}],
(* a list of matrices *)
MonodromyOnCharge[Drop[M,1],ch2tochi[{r,d,chi-r-3/2d} . {{0,0,-1},{0,1,0},{-1,0,0}} . Inverse[First[M]] . {{0,0,-1},{0,1,0},{-1,0,0}}]]]
];

MonodromyOnTau[M_,tau_]:=If[Length[M]==0,tau,If[
Depth[M]==3,
(* a single matrix *)
(M[[3,3]]tau+M[[3,2]])/(M[[2,3]]tau+M [[2,2]])
,(* a list of matrices *)
MonodromyOnTau[Drop[M,1],(M[[1,3,3]]tau+M[[1,3,2]])/(M[[1,2,3]]tau+M [[1,2,2]])]]
];

(* Fundamental domain centered around orbifold point, shifted by k along vertical axis *)
FundDomainC[k_]:=Graphics[{Thick,Blue,Line[{{k-1/2,Sqrt[3]/6},{k-1/2,1}}],
Line[{{k+1/2,Sqrt[3]/6},{k+1/2,1}}],Hue[.9],Circle[{k+1/3,0},1/3,{Pi/3,Pi}],Hue[.9],
Circle[{k-1/3,0},1/3,{0,2Pi/3}],Black,(*Dotted,
Circle[{k,0},1,{2Pi/3,Pi/3}],Circle[{k+1,0},1,{2Pi/3,Pi}],Circle[{k-1,0},1,{0,Pi/3}],
Line[{{k+1/2,1/2/Sqrt[3]},{k+1/2,Sqrt[3]/2}}],*)
Text["LV",{k,.9}],Text["o'",{k+.46,.35}],Text["o",{k-.46,.35}],Text["C",{k+.05,0.015}]
(*Text["LV",{k+.39,.02}],
Text["LV",{k-.39,.02}],
Text["C",{k+.05,0.02}],
Text["O",{k+.2,0.02}],
Text["O",{k-.19,0.02}],
Text["F",{k,1.1}],Text["g' F",{k-1/4,1/5}],
Text["g^('-1)F",{k+1/4,1/5}],Text[ToString[-1/2+k],{k-1/2,0.02}],Text[ToString[-1/2+k],{k+1/2,0.02}]*)}];

(* Fundamental domain centered around orbifold point, shifted by k along vertical axis *)
FundDomainO[k_]:=Graphics[{Thick,Line[{{k,0},{k,1}}],Line[{{k+1,0},{k+1,1}}],Hue[.9],
Circle[{k+1/3,0},1/3,{Pi/3,Pi}],Hue[.9],
Circle[{k+2/3,0},1/3,{0,2Pi/3}],Black,(*Dotted,
Circle[{k,0},1,{0,Pi/2}],
Circle[{k+1,0},1,{Pi/2,Pi}],
Line[{{k+1/2,1/2/Sqrt[3]},{k+1/2,Sqrt[3]/2}}],*)
Text["LV",{k+1/2,.9}],Text["C",{k+.95,0.02}],Text["C",{k+.05,0.02}],Text["o'",{k+.5,.33}]
(*Text["LV",{k+.27,.02}],Text["LV",{k+.73,.02}],
Text["C",{k+.45,0.02}],
Text["F",{k+1/2,1}],Text["g F",{k+1/3,1/5}],
Text["g^-1F",{k+2/3,1/5}],Text[ToString[k],{k-.03,0.02}],Text[ToString[k+1],{k+1.03,0.02}]*)}];

(* Fundamental domain centered around orbifold point and Z3 images, shifted by k along vertical axis *)
FundDomain3[k_]:=Graphics[{Red,Thick,
Circle[{k+1/3,0},1/3,{Pi/3,Pi}],Circle[{k+2/3,0},1/3,{0,2Pi/3}],Thin,
Line[{{k+1/2,0},{k+1/2,1/2/Sqrt[3]}}],Black,Thick,
Line[{{k,0},{k,1}}],Line[{{k+1,0},{k+1,1}}],Blue,Thin,
Circle[{k+1/6,0},1/6,{0,Pi}],Circle[{k+5/12,0},1/12,{0,Pi}],
Circle[{k+5/6,0},1/6,{0,Pi}],Circle[{k+7/12,0},1/12,{0,Pi}](*,Black,
Text["LV",{k+1/2,.7}],Text["C",{k+1,-0.04}],Text["C",{k,-0.04}],
Text["LV",{k+1/3,-.04}],Text["LV",{k+2/3,-0.04}],Text["C",{k+1/2,-0.04}],Text["O",{k+.5,.33}]*)
}];

FundDomainRulesC[k_]={{tau:>k+1/2+I/(2Sqrt[3]a)},{tau->k+1/3+1/3 Exp[I (1+2a)Pi/3]},{tau->k-1/2+I/(2Sqrt[3]a)},{tau->k-1/3+1/3 Exp[I 2a Pi/3]}};
FundDomainRulesO[k_]={{tau:>2I a+k},{tau->k+1/3+1/3 Exp[I (1+2a)Pi/3]},{tau->2I a+k+1},{tau->k+2/3+1/3 Exp[I 2a Pi/3]}};
FundDomainRules3[k_]={{tau:>k-1+2I a},{tau:>k+2I a},{tau:>k+1+2I a},{tau->k+1/6+1/6 Exp[I a Pi]},{tau->k+5/6+1/6 Exp[I a Pi]},{tau->k-1+1/6+1/6 Exp[I a Pi]},{tau->k-1+5/6+1/6 Exp[I a Pi]},{tau->k+5/12+1/12 Exp[I a Pi]},{tau->k+7/12+1/12 Exp[I a Pi]},{tau->k-1+5/12+1/12 Exp[I a Pi]},{tau->k-1+7/12+1/12 Exp[I a Pi]},{tau->k+1/3+1/3 Exp[I (1+2a)Pi/3]},{tau->k+2/3+1/3 Exp[I (2a) Pi/3]},{tau:>k+1/2+I a/2/Sqrt[3]},{tau->k-1+1/3+1/3 Exp[I (1+2a)Pi/3]},{tau->k-1+2/3+1/3 Exp[I (2a) Pi/3]},{tau:>k-1/2+I a/2/Sqrt[3]}};



(* ::Section:: *)
(*Evaluating periods via Eichler integrals*)


(* QuantumVolume has been divided by I, such that it is positive ! *)
(* QuantumVolume=N[27 Im[PolyLog[2,Exp[2I Pi/3]]]/4/Pi^2];*)
SetAttributes[QuantumVolume,Constant];
NumericQ[QuantumVolume]=True;
N[QuantumVolume,p___]:=N[27 Im[PolyLog[2,Exp[2I Pi/3]]]/4/Pi^2,p];
(* first 50 Fourier coefficients in C and C' :*)
FourierC={1,-9,27,-9,-117,216,27,-450,459,-9,-648,1080,-117,-1530,1350,216,-1845,2592,27,-3258,2808,-450,-3240,4752,459,-5409,4590,-9,-5850,7560,-648,-8658,7371,1080,-7776,10800,-117,-12330,9774,-1530,-11016,15120,1350,-16650,14040,216,-14256,19872,-1845,-22059,16227};
FourierCp={0,1,3,9,13,24,27,50,51,81,72,120,117,170,150,216,205,288,243,362,312,450,360,528,459,601,510,729,650,840,648,962,819,1080,864,1200,1053,1370,1086,1530,1224,1680,1350,1850,1560,1944,1584,2208,1845,2451,1803};
EichlerC[tau_]:=1+Sum[FourierC[[n+1]] Exp[2Pi I n tau],{n,Length[FourierC]-1}];
EichlerCp[taup_]:=Sum[FourierCp[[n+1]] Exp[2Pi I n taup],{n,Length[FourierCp]-1}];
Eichlerf1[tau_]:=2Pi I(tau+1/2)+Eichlerf1b[tau];
Eichlerf2[tau_]:=1/2 (2Pi I)^2(tau+1/2)^2+2Pi I(tau+1/2)Eichlerf1b[tau]+Eichlerf2b[tau];
Eichlerf1b[tau_]:=Sum[FourierC[[n+1]]/n Exp[2Pi I n tau],{n,Length[FourierC]-1}];
Eichlerf2b[tau_]:=-Sum[FourierC[[n+1]]/n^2 Exp[2Pi I n tau],{n,Length[FourierC]-1}];
Eichlerf1p[taup_]:=Sum[FourierCp[[n+1]]/n Exp[2Pi I n taup],{n,Length[FourierCp]-1}];
Eichlerf2p[taup_]:=2Pi I(taup)Eichlerf1p[taup]-Sum[FourierCp[[n+1]]/n^2 Exp[2Pi I n taup],{n,Length[FourierCp]-1}];
EichlerTLV[tau_]:=N[Eichlerf1[tau]/(2Pi I)-1/2];
EichlerTDLV[tau_]:=N[Eichlerf2[tau]/(2Pi I)^2-1/2Eichlerf1[tau]/(2Pi I)+1/4];
EichlerTC[tau_]:=N[27Sqrt[3]/(4Pi^2 I) Eichlerf2p[-1/(3 tau)]]+I*QuantumVolume;
EichlerTDC[tau_]:=N[-1/3 27Sqrt[3]/(2Pi)Eichlerf1p[-1/(3 tau)]];
EichlerZ[{r_,d_,chi_},tau_]:=EichlerZch2[{r,d,chi-r-3/2d},tau];
EichlerZch2[{r_,d_,ch2_},tau_/;Im[tau]==0]:={-ch2,d,-r} . ToFundDomainC[tau][[2]] . {1,I QuantumVolume,0};
EichlerZch2[{r_,d_,ch2_},tau_/;Im[tau]>0]:=Module[{ttau,M},
{ttau,M}=ToFundDomainCApprox[tau];
If[Im[ttau]>1/2/Sqrt[3],
Tr[{{-ch2,d,-r}} . M . {{1},{EichlerTLV[ttau]},{EichlerTDLV[ttau]}}],
Tr[{{-ch2,d,-r}} . M . {{1},{EichlerTC[ttau]},{EichlerTDC[ttau]}}]]];
EichlerZch2LV[{r_,d_,ch2_},tau_]:=-r EichlerTDLV[tau]+d EichlerTLV[tau]-ch2;
EichlerT[tau_]:=EichlerZch2[{0,1,0},tau];
EichlerTD[tau_]:=EichlerZch2[{-1,0,0},tau];
EichlerTtilde[tau_]:=EichlerZch2[{0,-1/2/Sqrt[3],-1/4/Sqrt[3]},tau];
EichlerTDtilde[tau_]:=EichlerZch2[{-1,-1/2,1/12},tau];

Initialtau1={};
Initialtau2={};

IntersectExactRaysLV[{r_,d_,chi_},{rr_,dd_,cchi_},psi_]:=
(* returns (tau1,tau2) coordinate of intersection point of two rays, or {} if they are collinear *)
Module[{tau1,tau2,Exacttau1,Exacttau2},
If[(r dd-rr d!=0) ,
If[TestBranch[{r,d,chi},(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr)]&&TestBranch[{rr,dd,cchi},(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr)],
            If[Length[Initialtau1]==0||Undefined[Initialtau1]||Length[Initialtau2]==0||Undefined[Initialtau2],{Initialtau1,Initialtau2}={(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr)-1/2Sin[psi]/Abs[r dd-rr d]\[Sqrt](4 cchi^2 r^2+4 chi^2 rr^2+4 chi (2 dd+3 rr) (dd r-d rr)+(dd r-d rr)^2+4 cchi (-2 d dd r-3 dd r^2+2 d^2 rr-2 chi r rr+3 d r rr)),1/2Cos[psi] /Abs[r dd-rr d]\[Sqrt](4 cchi^2 r^2+4 chi^2 rr^2+4 chi (2 dd+3 rr) (dd r-d rr)+(dd r-d rr)^2+4 cchi (-2 d dd r-3 dd r^2+2 d^2 rr-2 chi r rr+3 d r rr))}];
{Exacttau1,Exacttau2}={tau1,tau2}/.FindRoot[{Re[Exp[-I psi](-r EichlerTDLV[tau1+I tau2]+d EichlerTLV[tau1+I tau2]-(chi-3/2d-r))],Re[Exp[-I psi](-rr EichlerTDLV[tau1+I tau2]+dd EichlerTLV[tau1+I tau2]-(cchi-3/2dd-rr))]},{tau1,Initialtau1},{tau2,Initialtau2}];
{Initialtau1,Initialtau2}={Exacttau1,Exacttau2};If[Im[Exp[-I psi](-r EichlerTDLV[Exacttau1+I Exacttau2]+d EichlerTLV[Exacttau1+I Exacttau2]-(chi-3/2d-r))]>0&&Im[Exp[-I psi](-rr EichlerTDLV[Exacttau1+I Exacttau2]+dd EichlerTLV[Exacttau1+I Exacttau2]-(cchi-3/2dd-rr))]>0,Exacttau1+I Exacttau2,0]
,0]]];

IntersectExactRaysC[{r_,d_,chi_},{rr_,dd_,cchi_},psi_]:=
(* returns (tau1,tau2) coordinate of intersection point of two rays, or {} if they are collinear *)
Module[{tau1,tau2,Exacttau1,Exacttau2},If[(r dd-rr d!=0) ,If[TestBranch[{r,d,chi},(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr)]&&TestBranch[{rr,dd,cchi},(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr)],
If[Length[Initialtau1]==0||Undefined[Initialtau1]||Length[Initialtau2]==0||Undefined[Initialtau2],{Initialtau1,Initialtau2}={(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr)-1/2Sin[psi]/Abs[r dd-rr d]\[Sqrt](4 cchi^2 r^2+4 chi^2 rr^2+4 chi (2 dd+3 rr) (dd r-d rr)+(dd r-d rr)^2+4 cchi (-2 d dd r-3 dd r^2+2 d^2 rr-2 chi r rr+3 d r rr)),1/2Cos[psi] /Abs[r dd-rr d]\[Sqrt](4 cchi^2 r^2+4 chi^2 rr^2+4 chi (2 dd+3 rr) (dd r-d rr)+(dd r-d rr)^2+4 cchi (-2 d dd r-3 dd r^2+2 d^2 rr-2 chi r rr+3 d r rr))}];
{Exacttau1,Exacttau2}={tau1,tau2}/.FindRoot[{Re[Exp[-I psi](-r EichlerTDC[tau1+I tau2]+d EichlerTC[tau1+I tau2]-(chi-3/2d-r))],Re[Exp[-I psi](-rr EichlerTDC[tau1+I tau2]+dd EichlerTC[tau1+I tau2]-(cchi-3/2dd-rr))]},{tau1,Initialtau1},{tau2,Initialtau2}];
{Initialtau1,Initialtau2}={Exacttau1,Exacttau2};If[Im[Exp[-I psi](-r EichlerTDLV[Exacttau1+I Exacttau2]+d EichlerTLV[Exacttau1+I Exacttau2]-(chi-3/2d-r))]>0&&Im[Exp[-I psi](-rr EichlerTDLV[Exacttau1+I Exacttau2]+dd EichlerTLV[Exacttau1+I Exacttau2]-(cchi-3/2dd-rr))]>0,Exacttau1+I Exacttau2,0]
,0]]];

CriticalPsi[mu_]:=ArcTan[mu/QuantumVolume];
XY[tau_,psi_]:={Re[Exp[-I psi]EichlerT[tau]],-Re[Exp[-I psi]EichlerTD[tau]]}/Cos[psi];




(* ::Section:: *)
(*Bruno's routines*)


DtauT[tau_]:=(DedekindEta[tau]^3/DedekindEta[3tau])^3;
DtauZch2[{r_,d_,ch2_},tau_]:=(d-r tau)DtauT[tau];
DtauZ=DtauZch2;
ArgDtauT[tau_]:=Mod[9Arg[DedekindEta[tau]]-3Arg[DedekindEta[3tau]],2Pi,-Pi];
ArgDtauTD[tau_]:=Mod[Arg[tau]+9Arg[DedekindEta[tau]]-3Arg[DedekindEta[3tau]],2Pi,-Pi];
ArgDtauZch2[{r_,d_,ch2_},tau_]:= Mod[Arg[-r tau+d]+9Arg[DedekindEta[tau]]-3Arg[DedekindEta[3tau]],2Pi,-Pi];
UnitDtauT[tau_]:=Normalize[DedekindEta[tau]]^9 Normalize[DedekindEta[3tau]]^-3;
UnitDtauTD[tau_]:=Normalize[tau]UnitDtauT[tau];
UnitDtauZch2[{r_,d_,ch2_},tau_]:=Normalize[-r tau+d]UnitDtauT[tau];

NormalizeFunctionDomain[fun_InterpolatingFunction]:=Function@@{fun[Rescale[#,{0,1},fun["Domain"][[1]]]]};
NormalizeApprox[z_,eps_:0.001]:=z/(eps+Abs[z]);

Module[{solution,tangentfunction,a,taunum,boundaries,eventstop},IntegralCurve[tauinit_,tangent_,{ainit_,amin_,amax_},boundaries_List:{Im[tau]==0.01}]:=(eventstop=WhenEvent@@{boundaries/.tau->tau[a],"StopIntegration"};
tangentfunction[taunum_?NumericQ]=(If[Im[taunum]<=0,0,#]&[tangent/.tau->taunum]);
solution=tau/.Identity@@NDSolve[{tau[ainit]==tauinit,tau'[a]==tangentfunction[tau[a]],eventstop},tau,{a,amin,amax}];
NormalizeFunctionDomain[solution]);];

Module[{theta,tau1,tauinit,amin=-5,amax=5},
RayCh[psi_]:=RayCh[psi]=RayGeneralch2[{1,0,0},psi,1/((3(\[Pi]-theta))/(2\[Pi])-2.I),{theta,psi-Pi/2}];
RayGeneralch2[gamma:{_,_,_},psi_,tauexpr_,start_List]:=(
tauinit=tauexpr/.FindRoot[Re[Exp[-I psi]EichlerZch2LV[gamma,tauexpr]]==0,start];
IntegralCurve[tauinit,Normalize[EichlerZch2[gamma,tau]]Conjugate[UnitDtauZch2[gamma,tau]],{0,amin,amax},{Im[tau]==0.01(*,Norm[EichlerZch2[gamma,tau]]==10^-14*)}]);];

CPointch2[tau1:(_Integer|Rational[p_,q_/;Mod[q,3]!=0])]:=Inverse[ToFundDomainC[tau1][[2]]][[3]] . {{0,0,1},{0,-1,0},{1,0,0}};
TotalChargech2[(coef_:1) Ch[tau1:(_Integer|Rational[p_,q_/;Mod[q,3]!=0])][homshift_]]:=(-1)^homshift coef CPointch2[tau1];
TotalChargech2[(coef_:1) Ch[tau1:(_Integer|Rational[p_,q_/;Mod[q,3]!=0])]]:=coef CPointch2[tau1];
TotalChargech2[l_List]:=Sum[TotalChargech2[c],{c,Flatten[l]}];

CPointchi[tau1:(_Integer|Rational[p_,q_/;Mod[q,3]!=0])]:=ch2tochi[Inverse[ToFundDomainC[tau1][[2]]][[3]] . {{0,0,1},{0,-1,0},{1,0,0}}];
TotalChargechi[(coef_:1) Ch[tau1:(_Integer|Rational[p_,q_/;Mod[q,3]!=0])][homshift_]]:=(-1)^homshift coef CPointchi[tau1];
TotalChargechi[(coef_:1) Ch[tau1:(_Integer|Rational[p_,q_/;Mod[q,3]!=0])]]:=coef CPointchi[tau1];
TotalChargechi[l_List]:=Sum[TotalChargechi[c],{c,Flatten[l]}];

CPointxy[tau1:(_Integer|Rational[p_,q_/;Mod[q,3]!=0]),psi_]:=Re[Exp[-I psi]{1,-1}Drop[Flatten[ToFundDomainC[tau1][[2]] . {{1},{I QuantumVolume},{0}}],1]]/Cos[psi];

Module[{al},
ConifoldRay[init_,psi_,homshift_Integer:0]:=ConifoldRay[init]=
With[{dcba=ToFundDomainC[init][[2,2;;,2;;]]},
Function@@{al,(dcba[[2,1]]+dcba[[2,2]] RayCh[psi+2\[Pi]-\[Pi] homshift][al])/(dcba[[1,1]]+dcba[[1,2]] RayCh[psi+2\[Pi]-\[Pi] homshift][al])}];
];

TreeToRaysPlot[arg_List,psi_?NumericQ,plotoptions___]:=Show[Graphics[],Table[ParametricPlot[ReIm[ray[a]],{a,0,1},plotoptions],{ray,TreeToRays[arg,psi]}]];
TreeToRaysPlot[obj : _. Ch[_] | _. Ch[_][_], args___] := TreeToRaysPlot[{obj}, args];
TreeToRays[tree_,psi_]:=TreeToRays[tree,psi]=Flatten[{#[[3;;]],#[[2]]}]&@TreeToRaysch2[tree,psi];

Module[{amax=5,theta,gamma,gamma1,gamma2,rays1,lastray1,rays2,lastray2,a,a2,ainit,a2init,arules,aroot,a2root,tauinit,result},
  TreeToRaysch2[arg:((coef_:1) Ch[n_]), psi_?NumericQ] := TreeToRaysch2[coef Ch[n][0],psi];
  TreeToRaysch2[arg:{(coef_:1) Ch[n_],homshift_Integer}, psi_?NumericQ] := TreeToRaysch2[coef Ch[n][homshift],psi];
  TreeToRaysch2[arg:((coef_:1) Ch[n_][homshift_Integer]), psi_?NumericQ] :=
    {(-1)^homshift coef CPointch2[n], ConifoldRay[n,psi,homshift+If[coef>0,0,1]],{}};
  TreeToRaysch2[{trees_},psi_] := TreeToRaysch2[trees,psi]; (*for convenience, unary nodes are ok*)
  TreeToRaysch2[arg:{trees1_,trees2_},psi_?NumericQ] := (
    {{gamma1,lastray1,rays1},{gamma2,lastray2,rays2}} = {TreeToRaysch2[trees1,psi],TreeToRaysch2[trees2,psi]};
    arules={};
    If[lastray1=!={}&&lastray2=!={},
       Do[If[arules === {},  
	     arules = Check[FindRoot[ReIm@lastray1[a] == ReIm@lastray2[a2], {a, ainit, 0, 1}, {a2, a2init, 0, 1}],
			    {}, FindRoot::reged]],
	  {ainit, {0.1, 0.5, 0.9}}, {a2init, {0.1, 0.5, 0.9}}];
    ];
    If[arules==={},
       {gamma,{},Join[rays1,{lastray1},rays2,{lastray2}]}
     ,
       {aroot,a2root} = {a,a2}/.arules;
       tauinit=lastray1[aroot];
       gamma=gamma1+gamma2;
       {gamma,
	IntegralCurve[tauinit,Normalize[EichlerZch2[gamma,tau]]Conjugate[UnitDtauZch2[gamma,tau]],{0,0,amax},{Im[tau]==0.01,Norm[EichlerZch2[gamma,tau]]==10^-7}],
	Join[rays1,{Function@@{Simplify[lastray1[aroot Slot[1]]]}},
		 rays2,{Function@@{Simplify[lastray2[a2root Slot[1]]]}}]}
    ]);
];

StabilityWall[tree:{_,_},tauinit_]:=
  StabilityWall[tree,tauinit]=
  StabilityWall[tree,tauinit,{-2,2}];
StabilityWall[{tree1_,tree2_},tauinit_,{amin_,amax_}]:=
  StabilityWall[{tree1,tree2},tauinit,{amin,amax}]=
  With[{g1=TreeCharge[tree1],g2=TreeCharge[tree2]},
    IntegralCurve[Re[tauinit]+I tau2/.
        FindRoot[Im[EichlerZ[g1,Re[tauinit]+I tau2]/EichlerZ[g2,Re[tauinit]+I tau2]]==0,{tau2,Im[tauinit],0,+Infinity}],
      Conjugate@Normalize[DtauZ[g1,tau]/EichlerZ[g1,tau]-DtauZ[g2,tau]/EichlerZ[g2,tau]],{0,amin,amax},
      {Im[tau]==0.01,Norm[EichlerZ[g1,tau]]==10^-7,Norm[EichlerZ[g2,tau]]==10^-7}]];

RayFromInfinity[gamma:{r_,d_,chi_},psi_]:=
  RayFromInfinity[gamma,psi]=
  With[{t=1.},
    tauinit=s+I t/.FindRoot[Re[Exp[-I psi]EichlerZ[{r,d,chi},s+I t]]==0,
                            {s,If[r!=0,
                                  d/r-t Tan[psi]-Sign[r]/Cos[psi] Sqrt[t^2+2Disc[{r,d,chi}]Cos[psi]^2],
                                  (chi-3d/2-r)/d-t Tan[psi]]}];
    IntegralCurve[tauinit,-I Exp[I psi]Conjugate[UnitDtauZch2[gamma,tau]],{0,-10,10},
      {Im[tau]==0.2,Norm[EichlerZ[gamma,tau]]==10^-7}]];

      


(* ::Section:: *)
(*New routines in v1.5*)


ConstructLVDiagram[smin_,smax_,phimax_,Nm_,ListRays0_]:=Module[
{Inter,ListInter,ListRays,ListNewRays,kappa,KTab},
(* initial rays {charge, {x,y}, parent1, parent2,n1,n2 } *)
If[ListRays0=={},
         ListRays=Flatten[{
Table[{Ch[k],{k,-k^2/2},0,0,0,0},{k,Ceiling[smin],Floor[smax]}],
Table[{Ch[k][1],{k,-k^2/2},0,0,0,0},{k,Ceiling[smin],Floor[smax]}]},1]/.repCh;
   ListInter={};,
(* If list of rays is already provided *)
ListRays=ListRays0;
ListInter=Select[Table[{ListRays[[i,3]],ListRays[[i,4]]},{i,Length[ListRays]}],First[#]>0&]];
While[True,
ListNewRays={};
       Monitor[ Do[
If[  !MemberQ[ListInter,{i,j}],
AppendTo[ListInter,{i,j}];
 kappa=DSZ[ListRays[[i,1]],ListRays[[j,1]]];
If[kappa!=0,Inter=IntersectRaysNoTest[ListRays[[i,1]],ListRays[[j,1]],ListRays[[i,2]],ListRays[[j,2]]];
If[Inter!={},
KTab=KroneckerDims[Abs[kappa],Nm];
Do[If[CostPhi[KTab[[k,1]] ListRays[[i,1]]+KTab[[k,2]]ListRays[[j,1]],Inter[[1]]]<=phimax,
AppendTo[ListNewRays,{KTab[[k,1]]ListRays[[i,1]]+KTab[[k,2]]ListRays[[j,1]],Inter,i,j,KTab[[k,1]],KTab[[k,2]]}]],{k,Length[KTab]}]
]]]
,{i,Length[ListRays]},{j,i+1,Length[ListRays]}],{i,j}];
If[ListNewRays=={},Break[],
Print["Adding ",Length[ListNewRays], " rays, "];
ListRays=Flatten[{ListRays,ListNewRays},1];
]];
Print[Length[ListRays], " in total."];
ListRays];

(* Extract tree leading to k-th ray, internal *)
TreeFromListRays[ListRays_,k_]:=If[ListRays[[k,3]]==0,ListRays[[k,1]],{ListRays[[k,5]]TreeFromListRays[ListRays,ListRays[[k,3]]],ListRays[[k,6]]TreeFromListRays[ListRays,ListRays[[k,4]]]}];

(* Extract all trees leading to a ray with charge {r,d,chi} *)
LVTreesFromListRays[ListRays_,{r_,d_,chi_}]:=Module[{Lipos,Div,LiTrees},
Div=Divisors[GCD@@{r,d,chi}];
Lipos=Flatten[Join[Table[Position[ListRays,{r,d,chi}/k],{k,Div}]],1];
If[Lipos=={},
Print["No such dimension vector in the list"],
LiTrees=(GCD[r,d,chi]/GCD@@ListRays[[#,1]])TreeFromListRays[ListRays,#]&/@First[Transpose[Lipos]];
ScattSort[DeleteDuplicatesBy[SortBy[LiTrees,Length[TreeConstituents[#]]&],ScattGraph]
]]];

CostPhi[{r_,d_,chi_},s_]:=d-r s;

IntersectRaysNoTest[{r_,d_,chi_},{rr_,dd_,cchi_},z_,zz_]:=
(* returns (x,y) coordinate of intersection point of two rays, or {} if they don't intersect *)
(* here do not test if DSZ<>0, and require strictly in future of z and zz *)
Module[{zi},zi={(2 cchi r-3 dd r-2 chi rr+3 d rr)/(2 dd r-2 d rr),(cchi d-chi dd+dd r-d rr)/(-dd r+d rr)};
If[(zi-z) . {-r,d}>0&&(zi-zz) . {-rr,dd}>0,zi,{}]];

ClearAll[KroneckerDims];
KroneckerDims[m_,Nn_]:=KroneckerDims[m,Nn]=Module[{Ta={}},
Do[If[m n1 n2-n1^2-n2^2+1>=0&&GCD[n1,n2]==1,AppendTo[Ta,{n1,n2}]],{n1,0,Nn},{n2,0,Nn-n1}];Drop[Ta,2]];

InitialRaysOrigin={{1,0},{-1/2,-Sqrt[3]/2},{-1/2,Sqrt[3]/2}};

(* construct scattering diagram up to height phimax *)
ConstructMcKayDiagram[phimax_,ListRays0_]:=Module[{ListRays,ListInter,kappa,Inter,KTab,ListNewRays},
If[ListRays0=={},
(* initial rays {charge, {x,y}, parent1, parent2,n1,n2,level } *)
ListRays=Table[{IdentityMatrix[3][[k]],InitialRaysOrigin[[k]]-5 McKayVec[IdentityMatrix[3][[k]]],0,0,0,0,1},{k,3}];
ListInter={};,
(* If list of rays is already provided *)
ListRays=ListRays0;
ListInter=Select[Table[{ListRays[[i,3]],ListRays[[i,4]]},{i,Length[ListRays]}],First[#]>0&]];
While[True,
ListNewRays={};
       Monitor[ Do[
If[  !MemberQ[ListInter,{i,j}],
AppendTo[ListInter,{i,j}];
 kappa=McKayDSZ[ListRays[[i,1]],ListRays[[j,1]]];
If[kappa!=0,Inter=McKayIntersectRaysNoTest[ListRays[[i,1]],ListRays[[j,1]],ListRays[[i,2]],ListRays[[j,2]]];
If[Inter!={},
KTab=KroneckerDims[Abs[kappa],Floor[phimax/Min[Plus@@ListRays[[i,1]],Plus@@ListRays[[j,1]]]]];
Do[If[Plus@@(KTab[[k,1]] ListRays[[i,1]]+KTab[[k,2]]ListRays[[j,1]])<=phimax,
AppendTo[ListNewRays,{KTab[[k,1]]ListRays[[i,1]]+KTab[[k,2]]ListRays[[j,1]],Inter,i,j,KTab[[k,1]],KTab[[k,2]],ListRays[[i,7]]+ListRays[[j,7]]}]],{k,Length[KTab]}]
]]]
,{i,Length[ListRays]},{j,i+1,Length[ListRays]}],{i,j}];
If[ListNewRays=={},Break[],
Print["Adding ",Length[ListNewRays], " rays, "];
ListRays=Flatten[{ListRays,ListNewRays},1];
]];
Print[Length[ListRays], " in total."];
ListRays];

McKayIntersectRaysNoTest[Nvec_,NNvec_,z_,zz_]:=
(* require strict inequality *)
Module[{zi},zi=McKayIntersectRays[Nvec,NNvec];If[(zi-z) . McKayVec[Nvec]>0&&(zi-zz) . McKayVec[NNvec]>0,zi,{}]];

(* Extract all trees leading up to a ray with dimension vector {n1,n2,n3} *)
McKayTreesFromListRays[ListRays_,{n1_,n2_,n3_}]:=Module[{Lipos,Div,LiTrees},
Div=Divisors[GCD@@{n1,n2,n3}];
Lipos=Flatten[Join[Table[Position[ListRays,{n1,n2,n3}/k],{k,Div}]],1];
If[Lipos=={},
Print["No such dimension vector in the list"],
LiTrees=((n1+n2+n3)/Plus@@ListRays[[#,1]])TreeFromListRays[ListRays,#]&/@First[Transpose[Lipos]];
ScattSort[DeleteDuplicatesBy[SortBy[LiTrees,Length[TreeConstituents[#]]&],McKayScattGraph]
]]];

(* more careful implementation taking care of internal non-primitive states *)
Options[McKayScattIndexImprovedInternal] = {"Debug"->False};

McKayScattIndexImproved[TreeList_, opt: OptionsPattern[]]:=Table[
	(* compute index for each tree in the list *)
	Simplify[FOmbToOm[Last@McKayScattIndexImprovedInternal[TreeList[[i]], opt][[2]]]],{i,Length[TreeList]}];

McKayScattIndexImprovedInternal[Tree_, opt: OptionsPattern[]]:=Module[{S1,S2,g1,g2,gFinal, kappa,Li, tem, repOmAttb, rrr},
(* compute {total charge, list of Kronecker indices associated to each vertex *)
	If[!ListQ[Tree]||Length[Tree]>2,{Tree,{Join[{1}, Table[(y-y^-1)/(j(y^j-y^-j)), {j, 2, GCD@@Tree}]]}},
	If[OptionValue["Debug"], Print["Calling with args: ", Tree[[1]], "  |  ", Tree[[2]]]];
S1=McKayScattIndexImprovedInternal[Tree[[1]], opt]/.repChn;
	S2=McKayScattIndexImprovedInternal[Tree[[2]], opt]/.repChn;
If[OptionValue["Debug"], Print["S1 is: ", S1, "   S2 is: ", S2]];
	g1=GCD@@S1[[1]];g2=GCD@@S2[[1]];
gFinal = GCD@@(S1[[1]]+S2[[1]]);
	kappa=Abs[McKayDSZ[S1[[1]],S2[[1]]]]/g1/g2;
	Li=Join[S1[[2]],S2[[2]]];
If[OptionValue["Debug"], Print["Li is: ", Li, "  g1 is: ", g1, "  g2 is: ", g2, "  gFinal is: ", gFinal]];
AppendTo[Li,
repOmAttb = Join[
Table[CoulombHiggs`OmAttb[{P, 0}, y_]->Last[S1[[2]]][[P]], {P, 1, g1}],
Table[CoulombHiggs`OmAttb[{0, Q}, y_]->Last[S2[[2]]][[Q]], {Q, 1, g2}]
];
If[OptionValue["Debug"], Print["repOmAttb is: ", repOmAttb]];
tem = Table[
rrr = If[And@@(IntegerQ/@{P g1/gFinal, P g2/gFinal}), CoulombHiggs`FlowTreeFormulaRat[{{0, kappa}, {-kappa, 0}}, {g2, -g1}, {P g1/gFinal, P g2/gFinal}, y], 0];
Simplify[
rrr
/.repOmAttb
/.{CoulombHiggs`OmAttb[{p_, q_}, y___]:>0/;p>1||q>1||p q !=0}
],
{P, 1, gFinal}
];
If[OptionValue["Debug"], Print["tem is: ", tem]];tem
];
	{S1[[1]]+S2[[1]],Li}]];

(* more careful implementation taking care of internal non-primitive states *)
Options[ScattIndexImprovedInternal] = {"Debug"->False};
ScattIndexImproved[TreeList_, opt: OptionsPattern[]]:=Table[
	(* compute index for each tree in the list *)
	Simplify[FOmbToOm[Last@ScattIndexImprovedInternal[TreeList[[i]], opt][[2]]]],{i,Length[TreeList]}];

ScattIndexImprovedInternal[Tree_, opt: OptionsPattern[]]:=Module[{S1,S2,g1,g2,gFinal, kappa,Li, tem, repOmAttb, rrr},
(* compute {total charge, list of Kronecker indices associated to each vertex *)
	If[!ListQ[Tree]||Length[Tree]>2,{Tree,{Join[{1}, Table[(y-y^-1)/(j(y^j-y^-j)), {j, 2, GCD@@(Tree/.repCh)}]]}},
	If[OptionValue["Debug"], Print["Calling with args: ", Tree[[1]], "  |  ", Tree[[2]]]];
    S1=ScattIndexImprovedInternal[Tree[[1]], opt]/.repCh;
	S2=ScattIndexImprovedInternal[Tree[[2]], opt]/.repCh;
If[OptionValue["Debug"], Print["S1 is: ", S1, "   S2 is: ", S2]];
	g1=GCD@@S1[[1]];g2=GCD@@S2[[1]];
    gFinal = GCD@@(S1[[1]]+S2[[1]]);
	kappa=3Abs[(S1[[1,1]]S2[[1,2]] -S1[[1,2]]S2[[1,1]])/g1/g2];
	Li=Join[S1[[2]],S2[[2]]];
If[OptionValue["Debug"], Print["Li is: ", Li, "  g1 is: ", g1, "  g2 is: ", g2, "  gFinal is: ", gFinal," kappa is",kappa]];
AppendTo[Li,
repOmAttb = Join[
Table[CoulombHiggs`OmAttb[{P, 0}, y_]->Last[S1[[2]]][[P]], {P, 1, g1}],
Table[CoulombHiggs`OmAttb[{0, Q}, y_]->Last[S2[[2]]][[Q]], {Q, 1, g2}]
];
If[OptionValue["Debug"], Print["repOmAttb is: ", repOmAttb]];
tem = Table[
rrr = If[And@@(IntegerQ/@{P g1/gFinal, P g2/gFinal}),CoulombHiggs`FlowTreeFormulaRat[{{0, kappa}, {-kappa, 0}}, {g2, -g1}, {P g1/gFinal, P g2/gFinal}, y], 0];
Simplify[
rrr
/.repOmAttb
/.{CoulombHiggs`OmAttb[{p_, q_}, y___]:>0/;p>1||q>1||p q !=0}
],
{P, 1, gFinal}
];
If[OptionValue["Debug"], Print["tem is: ", tem]];tem
];
	{S1[[1]]+S2[[1]],Li}]];

FOmbToOm[OmbList_] := Module[{n},
If[Length[OmbList]<2, First@OmbList, 
n = Length[OmbList];
DivisorSum[n, (MoebiusMu[#] (y-y^-1)/(#(y^#-y^-#)) (OmbList[[n/#]]/.{y->y^#}))&]
]];



(* ::Section:: *)
(*Precomputed list of scattering trees at large volume*)


(* ::Input:: *)
(**)


LVTrees[{0,1,1}]={{-Ch[-1],Ch[0]}};
LVTrees[{0,2,0}]={{-2Ch[-2],2Ch[-1]}};
LVTrees[{0,2,1}]={{-Ch[-2],Ch[0]}};
LVTrees[{0,3,0}]={{-3Ch[-2],3Ch[-1]},{-Ch[-3],Ch[0]}};
LVTrees[{0,3,1}]={{{-2Ch[-2],Ch[-1]},Ch[0]}};
LVTrees[{0,4,0}]={{-4Ch[-2],4Ch[-1]},
{-Ch[-3],{{-Ch[-2],Ch[-1]},Ch[0]}}};
LVTrees[{0,4,1}]={{{-3Ch[-2],2Ch[-1]},Ch[0]},
{-Ch[-3],{-Ch[-1],2Ch[0]}}};
LVTrees[{0,4,2}]={{-2Ch[-2],2Ch[0]},
{{-2Ch[-2],Ch[-1]},{-Ch[-1],2Ch[0]}},
{-Ch[-3],Ch[1]}};
LVTrees[{0,5,0}]={{-5Ch[-2],5Ch[-1]},
{-Ch[-3],{{-2Ch[-2],2Ch[-1]},Ch[0]}},
{{-2Ch[-3],Ch[-2]},{-Ch[-1],2Ch[0]}},
{-Ch[-4],Ch[1]}};
LVTrees[{0,5,1}]={{{-4Ch[-2],3Ch[-1]},Ch[0]},
{-Ch[-3],{-Ch[-2],2Ch[0]}},
{{-Ch[-3],{-Ch[-2],Ch[-1]}},{-Ch[-1],2Ch[0]}},
{{-2Ch[-3],Ch[-2]},Ch[1]}};
LVTrees[{0,5,3}]={{-2 Ch[-2],{-Ch[-1],3 Ch[0]}},
{{-2 Ch[-2],Ch[0]},{-Ch[-1],2 Ch[0]}},
{{-2 Ch[-2],Ch[-1]},{-2 Ch[-1],3 Ch[0]}},
{{-3 Ch[-2],2 Ch[-1]},Ch[1]},
{-Ch[-3],{{-Ch[-1],Ch[0]},Ch[1]}}};
LVTrees[{0,6,1}]={{{-5 Ch[-2],4 Ch[-1]},Ch[0]},{-Ch[-3],{{-2 Ch[-2],Ch[-1]},2 Ch[0]}},{{-Ch[-3],{-Ch[-2],Ch[-1]}},{-Ch[-2],2 Ch[0]}},{{-Ch[-3],{-2 Ch[-2],2 Ch[-1]}},{-Ch[-1],2 Ch[0]}},{{-2 Ch[-3],Ch[-2]},{-2 Ch[-1],3 Ch[0]}},{{{-2 Ch[-3],Ch[-2]},{-Ch[-2],Ch[-1]}},Ch[1]},{{-2 Ch[-3],Ch[-1]},Ch[1]},{-Ch[-4],{{-Ch[-1],Ch[0]},Ch[1]}}};(* some tree is missing for (0,7,1) *)
LVTrees[{0,7,1}]={{{-6 Ch[-2],5 Ch[-1]},Ch[0]},{-2 Ch[-3],{-Ch[-1],3 Ch[0]}},{-Ch[-3],{{-3 Ch[-2],2 Ch[-1]},2 Ch[0]}},{{-Ch[-3],{-2 Ch[-2],2 Ch[-1]}},{-Ch[-2],2 Ch[0]}},{{-2 Ch[-3],Ch[0]},{-Ch[-1],2 Ch[0]}},{{-Ch[-3],{-3 Ch[-2],3 Ch[-1]}},{-Ch[-1],2 Ch[0]}},{{-2 Ch[-3],Ch[-2]},{-Ch[-2],{-Ch[-1],3 Ch[0]}}},{{-2 Ch[-3],Ch[-2]},{{-Ch[-2],Ch[0]},{-Ch[-1],2 Ch[0]}}},{{-2 Ch[-3],Ch[-1]},{-2 Ch[-1],3 Ch[0]}},{{{-2 Ch[-3],Ch[-2]},{-Ch[-2],Ch[-1]}},{-2 Ch[-1],3 Ch[0]}},{{-2 Ch[-3],{-Ch[-2],2 Ch[-1]}},Ch[1]},{{{-2 Ch[-3],Ch[-2]},{-2 Ch[-2],2 Ch[-1]}},Ch[1]},{-Ch[-4],{{-Ch[-2],Ch[0]},Ch[1]}},{{-Ch[-4],{-Ch[-2],Ch[-1]}},{{-Ch[-1],Ch[0]},Ch[1]}},{{-3 Ch[-3],2 Ch[-2]},{{-Ch[-1],Ch[0]},Ch[1]}},{{-Ch[-4],{-Ch[-3],Ch[-2]}},{-Ch[0],2 Ch[1]}},{{-2 Ch[-4],Ch[-3]},Ch[2]}};
(* Hilbert scheme of points *)
LVTrees[{1,0,0}]={{-Ch[-2],2Ch[-1]}};
LVTrees[{1,0,-1}]={{{-Ch[-3],Ch[-2]},Ch[-1]}};
LVTrees[{1,0,-2}]={{{-Ch[-4],Ch[-3]},Ch[-1]},{-2Ch[-3],3Ch[-2]}};
LVTrees[{1,0,-3}]={{{-Ch[-5],Ch[-4]},Ch[-1]},{{-Ch[-4],Ch[-3]},{-Ch[-3],2Ch[-2]}},{-Ch[-4],2Ch[-2]}};
LVTrees[{1,0,-4}]={{{-Ch[-6],Ch[-5]},Ch[-1]},{{-Ch[-5],Ch[-4]},{-Ch[-3],2Ch[-2]}},{{-2Ch[-4],2Ch[-3]},Ch[-2]}};
LVTrees[{1,0,-5}]={{{-Ch[-7],Ch[-6]},Ch[-1]},{{-Ch[-6],Ch[-5]},{-Ch[-3],2 Ch[-2]}},{{-Ch[-5],Ch[-4]},{{-Ch[-4],Ch[-3]},Ch[-2]}},{{-Ch[-5],Ch[-3]},Ch[-2]},{-3 Ch[-4],4 Ch[-3]}};
LVTrees[{1,0,-6}]={{{-Ch[-8],Ch[-7]},Ch[-1]},{{-Ch[-7],Ch[-6]},{-Ch[-3],2 Ch[-2]}},{{-Ch[-6],Ch[-5]},{{-Ch[-4],Ch[-3]},Ch[-2]}},{{-2 Ch[-5],2 Ch[-4]},Ch[-2]},{{-Ch[-5],Ch[-4]},{-2 Ch[-4],3 Ch[-3]}},{{-Ch[-5],Ch[-3]},{-Ch[-4],2 Ch[-3]}},{-Ch[-5],{-Ch[-4],3 Ch[-3]}}};
LVTrees[{1,0,-7}]={{{-Ch[-9],Ch[-8]},Ch[-1]},{{-Ch[-8],Ch[-7]},{-Ch[-3],2 Ch[-2]}},{{-Ch[-7],Ch[-6]},{{-Ch[-4],Ch[-3]},Ch[-2]}},{{-Ch[-6],Ch[-5]},{{-Ch[-5],Ch[-4]},Ch[-2]}},{{-Ch[-6],Ch[-5]},{-2 Ch[-4],3 Ch[-3]}},{{-Ch[-6],Ch[-4]},Ch[-2]},{{-2 Ch[-5],2 Ch[-4]},{-Ch[-4],2 Ch[-3]}},{{-Ch[-5],2 Ch[-3]},{-Ch[-5],Ch[-4]}},{{-2 Ch[-5],Ch[-4]},2 Ch[-3]}};
LVTrees[{1,0,-8}]={{{-Ch[-10],Ch[-9]},Ch[-1]},{{-Ch[-9],Ch[-8]},{-Ch[-3],2 Ch[-2]}},{{-Ch[-8],Ch[-7]},{{-Ch[-4],Ch[-3]},Ch[-2]}},{{-Ch[-7],Ch[-6]},{{-Ch[-5],Ch[-4]},Ch[-2]}},{{-Ch[-7],Ch[-6]},{-2 Ch[-4],3 Ch[-3]}},{{-2 Ch[-6],2 Ch[-5]},Ch[-2]},{{-Ch[-6],Ch[-5]},{-Ch[-5],2 Ch[-3]}},{{-Ch[-6],Ch[-5]},{{-Ch[-5],Ch[-4]},{-Ch[-4],2 Ch[-3]}}},{{-Ch[-6],Ch[-4]},{-Ch[-4],2 Ch[-3]}},{-Ch[-6],2 Ch[-3]},{{-3 Ch[-5],3 Ch[-4]},Ch[-3]}};
(*  higher rank D4-D2-D0 *)
LVTrees[{2,-1,0}]={{-Ch[-2],3Ch[-1]}};
LVTrees[{2,-1,-1}]={{{-Ch[-3],Ch[-2]},2Ch[-1]}};
LVTrees[{2,-1,-2}]={{{-Ch[-4],Ch[-3]},2Ch[-1]},{{-2Ch[-3],3Ch[-2]},Ch[-1]}};
LVTrees[{2,-1,-3}]={{{-Ch[-5],Ch[-4]},2 Ch[-1]},{{{-Ch[-4],Ch[-3]},{-Ch[-3],2 Ch[-2]}},Ch[-1]},{{-Ch[-4],2 Ch[-2]},Ch[-1]},{-3 Ch[-3],5 Ch[-2]}};
LVTrees[{2,0,0}]={{-2Ch[-2],4Ch[-1]}};
LVTrees[{2,0,-1}]={{-Ch[-3],3Ch[-1]},{{-Ch[-3],Ch[-2]},{-Ch[-2],3 Ch[-1]}}};
LVTrees[{2,0,-2}]={{{-Ch[-4],Ch[-3]},{-Ch[-2],3 Ch[-1]}},{{-2 Ch[-3],2 Ch[-2]},2 Ch[-1]}};
LVTrees[{3,-1,0}]={{-2 Ch[-2],5 Ch[-1]}};
LVTrees[{3,-1,-1}]={{{{-Ch[-3],Ch[-2]},Ch[-1]},{-Ch[-2],3 Ch[-1]}},{{-Ch[-3],Ch[-2]},{-Ch[-2],4 Ch[-1]}},{-Ch[-3],4 Ch[-1]}};
LVTrees[{3,-1,-2}]={{{-2 Ch[-3],2 Ch[-2]},3 Ch[-1]},
{{-Ch[-4],Ch[-3]},{-Ch[-2],4 Ch[-1]}},
{{-Ch[-2],3 Ch[-1]},{-2 Ch[-3],3 Ch[-2]}}};
LVTrees[{3,-1,-3}]={{2 Ch[-1],{-3 Ch[-3],4 Ch[-2]}},
{{-Ch[-4],Ch[-2]},3 Ch[-1]}};
(* trees are missing for (3,-1,-4), considered in Coskun Huizenga Woolf ex 7.7 *)
LVTrees[{3,-1,-4}]={{Ch[-1],{-4 Ch[-3],6 Ch[-2]}},
{2 Ch[-1],{-Ch[-4],{-Ch[-3],3 Ch[-2]}}},
{{-2 Ch[-4],2 Ch[-3]},3 Ch[-1]},
{{-Ch[-6],Ch[-5]},{-Ch[-2],4 Ch[-1]}}};
LVTrees[{3,1,4}]={{{-Ch[-1],3Ch[0]},Ch[0]},{-Ch[-1],4Ch[0]}};
LVTrees[{3,1,3}]={{{-Ch[-2],Ch[-1]},3 Ch[0]}};
LVTrees[{3,1,2}]={{2 Ch[0],{-2 Ch[-2],3 Ch[-1]}},{{-Ch[-3],Ch[-2]},3 Ch[0]}};
LVTrees[{3,0,0}]={{-3 Ch[-2],6 Ch[-1]}};
LVTrees[{3,0,-1}]={{{-Ch[-3],Ch[-2]},{-2 Ch[-2],5 Ch[-1]}},{{-Ch[-3],2 Ch[-1]},{-Ch[-2],3 Ch[-1]}}};
(* McKay trees *)
McKayTrees[{0,1,1}]={{{0,1,0},{0,0,1}}};
McKayTrees[{1,2,1}]={{{{1,0,0},{0,2,0}},{0,0,1}}};
McKayTrees[{1,2,2}]={{{{1,0,0},{0,2,0}},{0,0,2}}};
McKayTrees[{1,2,3}]={{{1,0,0},{{0,2,0},{0,0,3}}},{{{1,0,0},{0,2,0}},{0,0,3}}};
McKayTrees[{1,2,4}]={{{1,0,0},{{0,2,0},{0,0,4}}}};
McKayTrees[{2,2,4}]={{{2,0,0},{{0,2,0},{0,0,4}}}};
McKayTrees[{2,2,3}]={{{2,0,0},{{0,2,0},{0,0,3}}},{{{{1,0,0},{0,2,0}},{0,0,3}},{1,0,0}}};
McKayTrees[{2,3,3}]={{{{2,0,0},{0,3,0}},{0,0,3}},{{{{2,0,0},{0,0,1}},{0,3,0}},{0,0,2}}};
McKayTrees[{3,3,4}]={{{3,0,0},{{0,3,0},{0,0,4}}},{{2,0,0},{{{1,0,0},{0,3,0}},{0,0,4}}},{{2,0,0},{{{{1,0,0},{0,2,0}},{0,0,3}},{{0,1,0},{0,0,1}}}},{{{{{2,0,0},{0,0,1}},{0,3,0}},{0,0,3}},{1,0,0}}};
McKayTrees[{3,4,4}]={{{{{3,0,0},{0,0,1}},{0,4,0}},{0,0,3}},{{{{3,0,0},{{0,1,0},{0,0,2}}},{0,3,0}},{0,0,2}},{{{{{2,0,0},{0,0,1}},{0,3,0}},{{1,0,0},{0,1,0}}},{0,0,3}}};



End[];
EndPackage[]
