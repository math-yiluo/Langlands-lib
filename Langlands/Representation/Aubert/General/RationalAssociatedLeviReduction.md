# The rational associated-Levi comparison from published rational inputs

Author: Worker 757 (task `f7d95940-33d0-49d3-93d6-8d5ff8d89373`). The graded
exactness and top-degree surjectivity lemmas used in
`associatedGradedExactnessTarget_of_targets` are Worker 1252's modules
`CorrectedGradedExactness` and `CorrectedGradedTopSurjectivity` (task
`613611a4`). They build on Worker 691's `JacquetCutDiagram` and
`CorrectedDegreeFiltration`.

This module is a conditional reduction. It proves the exact rational target
`RationalPointFamily.RationalAssociatedLeviComparisonStatement.{u, v}` (module
`RationalTerminalJacquet`) in two forms.

* `rationalAssociatedLeviComparisonStatement_of_inputs` uses six
  propositions. Five are already in the Library: `RationalBruhatStatement`,
  `BruhatTits.DynamicParabolicQuotientCompactStatement`,
  `RationalCorrectedSurvivingSupportStatement`,
  `RationalCorrectedOrbitRadicalIntersectionStatement` and
  `RationalCorrectedOrbitSquaredModulusStatement`. The sixth is the
  proposition `RationalAssociatedGradedExactnessStatement`, defined in this
  module.
* `rationalAssociatedLeviComparisonStatement_of_published` uses seven
  propositions, all already in the Library: the five above,
  `RationalCorrectedGradedVanishingStatement` and
  `RationalCorrectedGradedTransitionStatement` (module
  `RationalCorrectedFiltrationTargets`). It replaces the sixth input of the
  first form by `rationalAssociatedGradedExactnessStatement_of_targets`.

The module proves none of these inputs and constructs no inhabitant of them.
The rational target therefore stays open until all seven published inputs are
proved.

Provenance: derived and internal. The inputs are the hypotheses of the
conditional theorem `TerminalJacquet.associatedLeviComparisonStatement_of_inputs`
(module `AssociatedLeviLongestRep`). That theorem assembles display (**) of
Aubert's 1996 erratum (p.4690, Remark (1)) along the corrected support
filtration of Ban–Jantzen (2016, Section 4). This module only instantiates that
theorem at the actual rational-point families. Its structure follows Worker
969's `rationalCorrectedGradedTransitionStatement_of_inputs` (module
`RationalCorrectedGradedReduction`).

## Declarations

* `TerminalJacquet.AssociatedGradedExactnessTarget P M U h hclosed hδ hP hU IsAssociate hM hLevi T actual`
  is a proposition template. It does not assert anything about an arbitrary
  family. Let `E` be any object of `supportObjects … I` and let `N` be the
  length of the decreasing-length enumeration of the Weyl group. Let `i` be any
  grade with `associatedGrade actual I < i < N`. The template asserts three
  properties of the associated graded maps
  `JacquetComplex.gradedDifferential E I i k` of the actual degree filtration:
  * they are surjective when `k + 1 = Complex.terminalDegree I`;
  * when `Complex.terminalDegree I = 1`, the map at `k = 0` is injective;
  * when `k + 2 = Complex.terminalDegree I`, the range of the map at `k` equals
    the kernel of the map at `k + 1`.

  These are exactly the hypotheses `hsurj`, `hinj` and `hex` of
  `associatedLeviComparisonStatement_of_inputs`.
* `TerminalJacquet.associatedGradedExactnessTarget_of_targets` proves
  `AssociatedGradedExactnessTarget` for general families. It assumes
  `hvan : CorrectedGradedVanishingTarget`,
  `htrans : CorrectedGradedTransitionTarget` (both at the coefficient universe
  `max uI uV`) and `hW : actualLeviWeylIdentification T M actual`. The proof
  takes `I`, `E` in the support category of `L_I`, and proves the three
  components separately.
  1. Surjectivity is Worker 1252's
     `JacquetComplex.gradedDifferential_surjective_top_of_leftDescentSet_eq`
     at `i₀ = associatedGrade actual I` (bound `associatedGrade_lt`) and
     `K₀ = associatedSubset actual I`. Its three Coxeter premises are the
     theorems of `AssociatedLeviDescent`:
     `mem_standardSubgroup_associatedSubset_iff_rankOrderedElement` (`hconj₀`),
     `length_lt_rankOrderedElement_associatedGrade_mul_simple` (`hR₀`) and
     `leftDescentSet_rankOrderedElement_associatedGrade` (`hD₀`).
  2. Injectivity is `JacquetComplex.gradedDifferential_injective_zero`. Its
     degree premise `0 < |S| - |I|` follows from
     `Complex.terminalDegree I = 1` after unfolding `terminalDegree`, by
     `omega`.
  3. Exactness is `JacquetComplex.gradedDifferential_range_eq_ker`. Its degree
     premise `k + 1 < |S| - |I|` follows from
     `k + 2 = Complex.terminalDegree I` in the same way.

  The last two lemmas hold at every grade, so the lower bound
  `associatedGrade actual I < i` is used only for surjectivity.
* `RationalPointFamily.isBruhatCover_standard` is a theorem about the actual
  standard parabolics. It assumes `RationalBruhatStatement`,
  `StandardParabolicEndpointsStatement` and `StandardParabolicOrderStatement`,
  and concludes
  `CorrectedFiltration.IsBruhatCover (torusPoints i) (parabolic i ν ∅) (parabolic i ν I)`
  for every `I`. In other words, every `g ∈ G(k)` is `p n q` with
  `p ∈ P_∅(k)`, `q ∈ P_I(k)` and `n` normalizing the torus image. Proof:
  1. The first endpoint identity together with `rootSet_empty` shows
     `parabolic i ν ∅ = P(ν)(k)`, the rational points of the dynamic parabolic
     of `ν ≫ i`.
  2. The covering half of `HasRationalBruhatDecomposition` writes `g = p n q`
     with `p, q ∈ P(ν)(k)` and `n ∈ normalizerPoints i`.
  3. `normalizerPoints_le_pointNormalizer` puts `n` in the normalizer of
     `torusPoints i`.
  4. `standardParabolic_monotone` moves `q` from `P_∅` into `P_I`.
* `RationalPointFamily.RationalAssociatedGradedExactnessStatement` is the
  rational instance of `AssociatedGradedExactnessTarget`. It is quantified over
  the same data and premises as `RationalCorrectedGradedTransitionStatement`
  and uses the decidable equality `Classical.decEq` on `Weyl i`. It is used as
  a hypothesis only and is not proved directly. The family it instantiates is
  the following:
  * the actual families `parabolic i ν`, `levi i ν` and `unipotent i ν`;
  * the semidirect decompositions `isSemidirectDecomposition_of_standardCocharacterStatement`;
  * unimodularity `standardUnipotent_isUnimodular i ν hU hUc`;
  * order `standardParabolic_monotone` and `standardUnipotent_antitone`;
  * association `rootAssociation i ν hN hZ`;
  * the Levi decompositions `isSemidirectDecomposition_in_levi`;
  * the torus image `torusPoints i` with the actual Coxeter system `cs`.
* `RationalPointFamily.rationalAssociatedGradedExactnessStatement_of_targets`
  proves `RationalAssociatedGradedExactnessStatement.{u, v}` from
  `hvan : RationalCorrectedGradedVanishingStatement.{u, v}` and
  `htrans : RationalCorrectedGradedTransitionStatement.{u, v}`. The proof
  introduces the statement's data and premises in order, and sets the same
  local instances as the statement: the point topology, the simple-root
  `Fintype` and `Classical.decEq` on `Weyl i`. It then applies
  `associatedGradedExactnessTarget_of_targets` to the actual families. The
  premises `hvan` and `htrans` are the two published statements at the same
  data. The premise `hW` is the statement's own
  `actualLeviWeylIdentification` premise. The vanishing statement does not
  take `hOrder` or `hUc`, so those two premises are not passed to it.
* `RationalPointFamily.rationalAssociatedLeviComparisonStatement_of_inputs`
  proves `RationalAssociatedLeviComparisonStatement.{u, v}` from the six inputs
  `hBr`, `hcompact`, `hsupp`, `hrad`, `hmod` and `hgr`. The proof introduces
  the target's data, sets `DecidableEq (Weyl i) := Classical.decEq _` as the
  input statements do, and applies
  `TerminalJacquet.associatedLeviComparisonStatement_of_inputs` at universes
  `u, u, max (u + 1) v`. It uses the target's own structural arguments, and
  supplies the theorem's remaining hypotheses as follows:
  * `SigmaCompactSpace` comes from `reductiveRationalPoint_secondCountable` and
    `sigmaCompactSpace_of_locallyCompact_secondCountable`;
  * compactness of every `P_J \ G` comes from `hcompact` through
    `compactSpace_leftQuotient_parabolic`;
  * `hPc` is `isClosed_standard_parabolic`, `hr` is
    `continuous_standard_projection`, and `hNc` is
    `isLimitOfCompactSubgroups_subgroupOf`; `hUc` is the target's own premise;
  * `hcover I` is `isBruhatCover_standard`;
  * `hsurj`, `hinj` and `hex` are the three components of `hgr`;
  * for a lift `n` of `longestRep actual I`, put `j = associatedGrade actual I`.
    By `rankOrderedElement_associatedGrade`, the `j`-th length-ordered element
    is `(longestRep actual I)⁻¹`, so `n` lifts its inverse. `H I n hn` is then
    `hsupp` at `s = associatedCoordinate actual I` and grade `j`, with the
    minimality `isMinimal_associatedCoordinate`;
  * `hS1` and `hS2` are the two components of `hrad` at grade `j`,
    `K = associatedSubset actual I` and `m = n`. They use the membership
    equivalence `x ∈ L_I ↔ n⁻¹ x n ∈ L_{I'}`, derived from `hAssociated`
    exactly as the target's `hnM`;
  * `hD07 I n hn hK` is `hmod` at the same grade, `K = associatedSubset actual I`
    and the given `hK`.
* `RationalPointFamily.rationalAssociatedLeviComparisonStatement_of_published`
  proves `RationalAssociatedLeviComparisonStatement.{u, v}` from `hBr`,
  `hcompact`, `hsupp`, `hrad`, `hmod`, `hvan` and `htrans`. It is
  `rationalAssociatedLeviComparisonStatement_of_inputs` with
  `hgr = rationalAssociatedGradedExactnessStatement_of_targets hvan htrans`.

## Remaining inputs

The rational target follows once the seven published inputs of
`rationalAssociatedLeviComparisonStatement_of_published` are proved. This
module adds no input of its own beyond those Library propositions.
