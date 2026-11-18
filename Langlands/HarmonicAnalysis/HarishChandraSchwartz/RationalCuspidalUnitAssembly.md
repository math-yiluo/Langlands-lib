# Proposition VIII.4.1 from a degree-zero operator and four analytic statements

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, literature ID `waldspurger-2003-plancherel`.
Relevant passage: the proof of Proposition VIII.4.1, printed pp. 328–330
(PDF pp. 94–96).

This module belongs to unit 3 ("rank adapter") of Task 7439, revision 2. Its
provenance is **derived**. It contains no new analysis. It composes modules of
the same task with each other and with Library statements. It names one new
proposition, `RationalDegreeZeroOperatorExistenceStatement`, and does not prove it.

* `RationalCuspidalUnitKernel` (unit 3) defines `IsRationalDegreeZeroOperator`,
  the six degree-zero laws of a complex-linear operator `P` on the actual rational
  Schwartz space. It proves that `°e = P(1_H)` satisfies
  `IsRationalCuspidalLevelKernel` and, from the closed Corollary VIII.3.2
  statement, `RationalLevelKernelConjugationIntegrable`.
* `RationalCuspidalCentralKernelLocalStep` (Worker 825's follow-up of unit 2)
  proves that these two properties of an element `E`, together with the central
  and `L²` weights, make the actual central level span finite dimensional for
  connected reductive `G` and every unitary `χ`
  (`IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan_of_conjugationIntegrable`).
  It also proves the closed form `RationalCuspidalLevelKernelFiniteStatement` from
  three Library statements (`RationalCuspidalLevelKernelFiniteStatement.of_statements`).
* `RationalCuspidalCentralImage` and `RationalCuspidalCentralFiniteReduction`
  (unit 1) give the equality of the span with the raw image under central
  convergence (`coe_schwartzCentralIntegralSpan_eq_image`,
  `CentralIntegralConvergesOn.mono_of_le`).
* `RationalCuspidalConvergenceReductions` (Library) derives closed central
  convergence from the split-centre heights
  (`RationalSplitCenterHeightStatement.schwartzCentralConvergence`).

## What the source does

The proof of VIII.4.1 first disposes of the case where `χ` is nontrivial on
`A_G ∩ H`. Otherwise it takes `e = 1_H` and the degree-zero projection
`°e` of VIII.2. It uses the properties of `°e` (p. 328), the reproducing formula
from Lemma VIII.2.3, and the finite diagonal integral from Corollary VIII.3.2
(p. 329) to show that the central level image is finite dimensional
(pp. 329–330). This module assembles the formalized pieces of that argument for
one group, and then for all groups at once.

## What this module proves

Throughout, `hKc`, `hPK` and `ρ` are the structural data of the actual rational
Schwartz space, as in `RationalCuspidalCentralProjectionFiniteStatement`.

* `IsRationalDegreeZeroOperator.finiteDimensional_levelSpan_of_conjugationIntegrable`.
  Hypotheses: `G` connected reductive, `IsSplitComponent s`, a Haar measure `muA`
  on `A_G(F) = (rationalPoints.map s).range`, a unitary character `χ`, a Haar
  measure `μG` on `G(F)`, `IsRationalDegreeZeroOperator hKc hPK ρ μG P`, a compact
  open subgroup `H`, `CentralWeights muA Ξ σ`, `L2Weights μG Ξ σ` (with
  `Ξ = rationalXi hKc hPK`, `σ = rationalHeight ρ`) and
  `RationalLevelKernelConjugationIntegrable hKc hPK ρ hs muA μG (P e)`, where
  `e = rationalSubgroupIndicator hKc hPK ρ μG H`. Conclusion:
  `FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup)`.
  Proof: `IsRationalDegreeZeroOperator.isRationalCuspidalLevelKernel` followed by
  the local step of `RationalCuspidalCentralKernelLocalStep`.
* `IsRationalDegreeZeroOperator.centralLevelSpan_eq_image_and_finiteDimensional`:
  **Proposition VIII.4.1 for one group.** Hypotheses: the four closed Library
  statements `RationalSplitCenterHeightStatement`,
  `RationalXiSquareIntegrableStatement`,
  `CuspidalSupport.RationalSpecialVertexCompactInputsStatement` and
  `RationalCuspidalConjugationIntegrabilityStatement`; `G` connected reductive,
  `IsMaximalSplitTorus i`, `IsGenericCocharacter i ν`, `IsClosedSubgroup ρ`,
  `IsSplitComponent s`; one Haar measure `μG` on `G(F)` and one operator `P` with
  `IsRationalDegreeZeroOperator hKc hPK ρ μG P`. Conclusion: for every Haar
  measure `muA` on `A_G(F)`, every continuous unitary character `χ` and every
  compact open subgroup `H`, the carrier of
  `rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup` equals
  `rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H.toSubgroup`, and the span is
  finite dimensional over `ℂ`. This is the body of
  `RationalCuspidalCentralProjectionFiniteStatement` at the given structural data.
  Proof:
  * equality: the split-centre heights give closed central convergence, which
    restricts to the level and gives the equality (as in unit 1);
  * finiteness: the special-vertex statement supplies a compact `K0` with
    `SimultaneousStandardBasisAt i ν K0`. With it, unit 3 gives
    `RationalLevelKernelConjugationIntegrable` at `°e = P(1_H)` from VIII.3.2.
    Unit 3 also gives `IsRationalCuspidalLevelKernel` at `°e`.
    `RationalCuspidalLevelKernelFiniteStatement.of_statements` then concludes; it
    takes the central and `L²` weights from the first three statements and splits
    off the case where `χ` is nontrivial on `A_G(F) ∩ H`.

### The named proposition (definition, entry declaration)

`RationalDegreeZeroOperatorExistenceStatement` says: for every nonarchimedean
local field `F`, every affine, locally finite type, connected reductive `G`, every
maximal split torus `i`, generic cocharacter `ν`, compact open `K` with
`IsIwasawaPair (standardParabolicPoints i ν ∅) K` and closed matrix
representation `ρ` (the structural data of
`RationalCuspidalCentralProjectionFiniteStatement` before the split component),
there are a measure `μG` on `G(F)` with `μG.IsHaarMeasure` and a complex-linear
operator `P` on `RationalSchwartzSpace hKc hPK ρ` with
`IsRationalDegreeZeroOperator hKc hPK ρ μG P`.

In the source, `P` is the degree-zero projection `f ↦ °f` of VIII.2, and the six
laws are Lemma VIII.2.1, the translation relation of the proof of VIII.4.1,
Remark VIII.2.2 and Lemma VIII.2.3. The proposition asks only for some operator
with the laws, not for that specific one.

* `RationalDegreeZeroOperatorExistenceStatement.centralProjectionFinite`: this
  proposition and the four Library statements above imply
  `RationalCuspidalCentralProjectionFiniteStatement`. Proof: obtain `μG` and `P`
  for the given structural data and apply the previous theorem.

## How this relates to the rank recursion

The source constructs `°f` for `G` from results on proper Levi subgroups
(strictly smaller relative rank). The per-group theorem
`IsRationalDegreeZeroOperator.centralLevelSpan_eq_image_and_finiteDimensional`
uses one operator for the one group `G` and no statement about `G` itself
besides the four analytic Library statements. It is the form for a well-founded
assembly over rank (Task 3642). The closed corollary assumes the existence of
such an operator for every group at once. It records what the closed target
still needs and does not by itself discharge the recursion.

## Open hypotheses and their owners

No hypothesis here is same-rank finiteness, same-rank reconstruction, the
closed target or a dimension bound.

* `RationalSplitCenterHeightStatement`: owned by **Task 5480**.
* `RationalXiSquareIntegrableStatement` (Lemma II.1.5): the Library proves it
  from `RationalXiUpperBoundStatement` by
  `rationalXiSquareIntegrable_of_upperBound`; that upper bound is owned by
  **Task 5326**.
* `CuspidalSupport.RationalSpecialVertexCompactInputsStatement`: the Library
  proves it from `JointSpecialCompactBasisExistenceStatement` by
  `CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis`; that
  statement is owned by **Task 4169**.
* `RationalCuspidalConjugationIntegrabilityStatement` (Corollary VIII.3.2): its
  proof is owned by **Task 7500**.
* `RationalDegreeZeroOperatorExistenceStatement`, or for one group an operator
  with `IsRationalDegreeZeroOperator`: the actual degree-zero projection and its
  VIII.2.1–VIII.2.3 laws are owned by **Task 7277**. Worker 3642 has assigned the
  translation law to Task 7277 as well. Discharging `IsRationalDegreeZeroOperator`
  for Task 7277's operator is Task 7439's unit 3, after Task 7277 publishes. The
  well-founded assembly over rank is owned by **Task 3642**.

The closed target `RationalCuspidalCentralProjectionFiniteStatement` is not
proved here. This module is an intermediate unit; Task 7439's completion still
requires the closed theorem.

## Dependencies

This module imports `RationalCuspidalUnitKernel` (Task 7439 unit 3, candidate
`6dd35692-0689-4a5b-8236-bde0f31d78c0`, staged, not yet in the Library),
`RationalCuspidalCentralKernelLocalStep` (Task 7439, Worker 825's unit published
as candidate `b46ce0f0-0164-4091-b359-d77221dc0431`) and the Library module
`RationalCuspidalConvergenceReductions`.
