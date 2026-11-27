# Proposition VIII.4.1 at the degree-zero operator of VIII.2

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI [10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082), literature ID
`waldspurger-2003-plancherel`. Relevant passages: the construction of `°f` at the start of
VIII.2 and Lemma VIII.2.1, Remark VIII.2.2 and Lemma VIII.2.3, printed pp. 321–322
(PDF pp. 87–88); Proposition VIII.4.1 and its proof, printed pp. 327–330 (PDF pp. 93–96).

The provenance of this module is **derived**. It contains no new analysis: it connects the
actual operator `rationalSemistandardDegreeZero` (`°f = f - κ(ψ)`, module
`RationalSemistandardDegreeZero`) with the proof of Proposition VIII.4.1 at an abstract
operator with the degree-zero laws (module `RationalCuspidalUnitAssembly`). It names one
proposition, `RationalSemistandardDegreeZeroCentralFiniteStatement`, and proves it
(`rationalSemistandardDegreeZeroCentralFinite`).

## What the source does

In the proof of VIII.4.1, after the case where `χ` is nontrivial on `A_G ∩ H`, Waldspurger
takes `e = 1_H` and its image `°e` under the operator `f ↦ °f` of VIII.2. He uses that `°e`
lies in `°C(G)` (Lemma VIII.2.1), the translation relation `°(ρ(g₁)λ(g₂)f) = ρ(g₁)λ(g₂)°f`,
the symmetries of Remark VIII.2.2 (with `f ↦ fˇ`, complex conjugation and unitary unramified
twists) and the reproducing formula from Lemma VIII.2.3 (p. 328), and the finite diagonal
integral of Corollary VIII.3.2 (p. 329), to show that the central level image is finite
dimensional (pp. 329–330). The operator `°f` exists for `G` because Theorems VIII.1.1 and
VIII.1.2 are assumed for all groups of strictly smaller semisimple rank (p. 321).

## Setting

The field is any nonarchimedean local field `F` with finite residue field, in any
characteristic; the group is any affine, locally finite type, connected reductive group
scheme over `F`, with no split or quasi-split assumption and including relative rank zero
(where the operator is the identity, `rationalSemistandardDegreeZero_eq_id_of_rank_zero`).
The field universe `u` and the universe `uV` of the representation carriers in the Fourier
data are independent. The parameters of the operator are exactly those of
`rationalSemistandardDegreeZero` in `RationalSemistandardDegreeZero`: the semistandard index
data `a`, `ha`, `muM`, `d`, the comparison data `C`, the maximal split torus `i`, generic
cocharacter `nu`, Iwasawa compact `K`, matrix representation `rho`, an ambient measure `muG`
(here a Haar measure that is right invariant and s-finite, as in
`RationalSemistandardDegreeZeroConvolution`), the square-integrable weight, modular
normalizations and tempered coefficients of the Fourier family, its construction inputs
(`hgeo`, `hcomp`, the strictly lower-rank local finiteness `hlow`, smoothness `hS`, the
analytic inputs `hin`, the proper/group split `hsplit`, VII.1.4 covariance `hcov`) and the
synthesis data (`rs`, `hindex`, `Q`, `K0`, `hK0`, `hfiber`, `hmem`, `hspecial`, `hd`, `hQ`).

## Declarations

* `rationalSemistandardDegreeZero_rangeLaw_of_kernelComparison`: the conclusion
  `RationalSemistandardDegreeZeroKernelComparison` of Lemma VIII.2.1 for the operator gives
  `RationalDegreeZeroRangeLaw` (every `°f` lies in `rationalCuspidalSubmodule`). Proof: its
  first conjunct identifies `LinearMap.range` of the operator with
  `rationalCuspidalSubmodule`.
* `rationalSemistandardDegreeZero_isRationalDegreeZeroOperator`: **the six degree-zero laws
  for the actual operator.** Given `ConvolutionWeights muG K Ξ σ` (for
  `Ξ = rationalXi hKc hPK`, `σ = rationalHeight rho`) and the premises listed below, the
  operator satisfies `IsRationalDegreeZeroOperator hKc hPK rho muG` (module
  `RationalCuspidalUnitKernel`). Proof, law by law:
  * range: `rationalSemistandardDegreeZeroKernel` (the conditional Lemma VIII.2.1) at the
    VIII.2.1 premises, then the previous theorem;
  * translation: `rationalSemistandardDegreeZero_translationLaw`, which needs no premise
    beyond the operator's construction;
  * conjugation, check and unitary twist: `rationalSemistandardDegreeZero_conjLaw`,
    `rationalSemistandardDegreeZero_checkLaw` and `rationalSemistandardDegreeZero_twistLaw`
    (Remark VIII.2.2) at the two symmetry premises;
  * left convolution: `rationalSemistandardDegreeZero_leftConvolutionLaw` (Lemma VIII.2.3)
    at the convolution weights and the two convolution premises, for the same `muG` as in
    the Fourier family.
* `RationalSemistandardDegreeZeroCentralFiniteStatement` (entry declaration, a
  proposition depending on the operator's parameters): under the premises listed below,
  the operator satisfies `IsRationalDegreeZeroOperator hKc hPK rho muG`, and for every split
  component `s : Z.toGrp ⟶ G` (`IsSplitComponent s`), every Haar measure `muA` on
  `A_G(F) = (rationalPoints.map s).range`, every continuous unitary character `χ` of
  `A_G(F)` and every compact open subgroup `H` of `G(F)`, the carrier of
  `rationalCuspidalCentralLevelSpan hKc hPK rho muA χ H.toSubgroup` equals
  `rationalCuspidalCentralLevelImage hKc hPK rho muA χ H.toSubgroup` and the span is finite
  dimensional over `ℂ`. The second conjunct is the body of
  `RationalCuspidalCentralProjectionFiniteStatement` at the structural data of `G`.
* `rationalSemistandardDegreeZeroCentralFinite`: proof of that proposition. The first
  conjunct is `rationalSemistandardDegreeZero_isRationalDegreeZeroOperator`. The second
  applies `IsRationalDegreeZeroOperator.centralLevelSpan_eq_image_and_finiteDimensional`
  (module `RationalCuspidalUnitAssembly`) to the operator, with the split-centre heights
  `rationalSplitCenterHeight` (module `RationalSplitCenterHeightProof`), Lemma II.1.5 in the
  form `rationalXiSquareIntegrable_of_upperBound rationalXiUpperBound` (modules
  `RationalXiSquareIntegrableOfUpperBound` and `RationalXiUpperBoundProof`), and the two
  closed premises below. Through that theorem, the equality with the raw image comes from
  closed central convergence and the finiteness from the local kernel step at
  `°e = °(1_H)`.

## Premises of the proposition

Each premise is an explicit hypothesis of `RationalSemistandardDegreeZeroCentralFiniteStatement`
(in this order); this module proves none of them.

| Premise | Role | Predicates defined in |
| --- | --- | --- |
| `RationalSemistandardDegreeZeroInverseInput` (VII.2.5 at the operator's data) | projector algebra of VIII.2.1 | `RationalSemistandardDegreeZeroKernel` |
| `RationalCuspidalSemistandardComparisonStatement`, `IsClosedSubgroup rho` | the intrinsic kernel as vanishing of all proper semistandard induced constant terms | `RationalCuspidalSemistandardComparison` |
| VII.1.2 analytic inputs `RationalSemistandardFourierAnalyticInputs` at every proper index (with a Haar radical measure) | identity of the operator on `rationalCuspidalSubmodule` | `RationalSemistandardFourierFamily` |
| outer-Levi data `c p : RationalSemistandardLeviFourierData`, source-normalized data `src p : RationalSourceFourierData` and `SourceFourierTransferAt` for every `f^M` | the function `f^M` on each proper Levi and the change of normalization | `RationalSemistandardFourierDetection`, `RationalSemistandardDegreeZeroKernel` |
| `RationalStrictlyLowerRankSynthesisReconstructionStatement (relativeRootRank i)` | VIII.1 (2) for all groups of strictly smaller relative semisimple rank; detection in VIII.2.1 | `RationalSemistandardDegreeZeroKernel` |
| `SemistandardInducedCharacterSymmetryStatement`, `GlobalSynthesis.ProperOrbitSymmetryStatement` | Remark VIII.2.2 | `RationalSemistandardFourierCharacterSymmetry`, `RationalSemistandardProperOrbitSymmetry` |
| `GlobalSynthesis.ComponentContinuityStatement`, `GlobalSynthesis.ProperPacketConvolutionVanishingStatement` (for `muG`) | Lemma VIII.2.3 | `RationalSemistandardWeightedSynthesis`, `RationalSemistandardProperSynthesisConvolution` |
| `ConvolutionWeights muG K Ξ σ` | the Schwartz convolution through which Lemma VIII.2.3 is stated | `Convolution` |
| `CuspidalSupport.RationalSpecialVertexCompactInputsStatement` | a special compact `K0` with `SimultaneousStandardBasisAt` and a finite Cartan covering, used for the `L²` weights and for VIII.3.2 at `°e` | `RationalCuspidalInertiaDecompositionReduction` |
| `RationalCuspidalConjugationIntegrabilityStatement` | Corollary VIII.3.2, the finite diagonal integral at `°e` | `RationalCuspidalConjugationStatement` |

`ConvolutionWeights` is a premise because the Library's constructor
`rationalConvolutionWeights` (module `RationalXiSquareIntegrable`) needs `K` inside
`rationalHeightSubgroup rho` (Waldspurger's `τ(K) ⊂ GL_n(𝒪)`, I.1), which the structural
data here do not include. The special-vertex statement follows from
`JointSpecialCompactBasisExistenceStatement` by
`CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis`.

## The rank recursion

The two strictly lower-rank inputs of VIII.2 enter separately: local VIII.1.2 finiteness in
strictly smaller rank (`hlow`, a parameter of the operator) gives the finite support of the
proper Fourier truncation and hence the operator; VIII.1 (2) in strictly smaller rank is a
premise used only for the range law (detection of zero constant terms). Neither predicate
mentions `G`, and the remaining premises are statements about `G`'s Fourier and synthesis
data or closed statements that do not involve VIII.4.1. No premise is same-rank finiteness,
same-rank reconstruction, `RationalCuspidalCentralProjectionFiniteStatement` or a dimension
bound. The proposition is therefore a local VIII.4.1 step at relative rank
`relativeRootRank i`, in the form used by an induction on the relative semisimple rank. It
concerns one group with its data; it is not the closed statement
`RationalCuspidalCentralProjectionFiniteStatement`, which this module does not prove.

## Dependencies

This module imports `RationalSemistandardDegreeZeroKernel`,
`RationalSemistandardDegreeZeroSymmetry`, `RationalSemistandardDegreeZeroConvolution`,
`RationalCuspidalUnitAssembly`, `RationalSplitCenterHeightProof`, `RationalXiUpperBoundProof`
and `RationalXiSquareIntegrableOfUpperBound`.
