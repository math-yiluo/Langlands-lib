# The rational surviving graded transitions from explicit structural inputs

Module: `Langlands.Representation.Aubert.General.RationalCorrectedGradedReduction`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

This module is a conditional helper. It has one definition and one theorem:

* `RationalCorrectedGradedTransitionInputs.{u}`: a proposition that lists
  three structural facts about the actual standard families on
  `RationalPoint k G.X`;
* `rationalCorrectedGradedTransitionStatement_of_inputs`: from
  `H : RationalCorrectedGradedTransitionInputs.{u}` it proves the exact Library
  proposition `RationalCorrectedGradedTransitionStatement.{u, v}`
  (RationalCorrectedFiltrationTargets), for every universe `v`.

The module does not prove `RationalCorrectedGradedTransitionStatement` outright,
because it constructs no inhabitant of the inputs. The topological assumptions
of the generic reduction that the Library already proves are not inputs. The
theorem obtains them from the published theorems listed under "The theorem"
below:

* σ-compactness of `RationalPoint k G.X`;
* closedness of the standard parabolics;
* continuity of the Levi projections.

The three input facts are the remaining ones. The section "Status of the
inputs" records what the Library offers for them.

## The definition

`RationalCorrectedGradedTransitionInputs.{u}` uses the same binders as
`RationalCorrectedGradedTransitionStatement.{u, v}`, in the same order:

* the nonarchimedean local field `k`;
* the connected reductive `G` with maximal split torus `i : T → G`;
* the point topology on `RationalPoint k G.X` with its local compactness,
  nonarchimedean and Hausdorff instances;
* the generic cocharacter `ν`;
* the named propositions `hStandard`, `hOrder`, `hInter`;
* the relative root system `hRoots` and the comparisons `hN` and `hZ`;
* the closedness premises `hU`, `hM` and the limit premise `hUc`;
* the linear order on the simple roots and the finiteness of `Weyl i`;
* the Coxeter matrix `CM` with the actual Coxeter system `cs` and its three
  comparison hypotheses.

The binders `hOrder`, `hInter`, `hM` and `hUc` are not used in the conclusion
and are written `_hOrder`, `_hInter`, `_hM`, `_hUc`. The definition does not
mention representations, so it has only the universe `u`.

Notation:

* `h` is `isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν`;
* `P_J`, `M_J`, `U_J` are `parabolic i ν J`, `levi i ν J`, `unipotent i ν J`;
* `J = S \ s` is `Finset.univ \ s`;
* at grade `n < (rankOrderedList cs.length).length`, `w` is
  `Support.rankOrderedElement cs.length n hn`;
* `m : Group.RelativeWeyl.normalizer (torusPoints i)` is a lift of `w⁻¹`,
  that is, `(QuotientGroup.mk m : Weyl i) = w⁻¹`;
* `J` is surviving when `IsMinimal cs (Finset.univ \ s) I w`.

Under these binders the conclusion is the conjunction of the following three
facts.

1. Every quotient `Induction.LeftQuotient P_J`, i.e. `P_J \ G`, is compact.
2. For all `I`, `s`, `n`, `hn` and every lift `m` of `w⁻¹` with `J` surviving:
   `CorrectedFiltration.SurvivingSupportHypotheses (parabolic i ν) (torusPoints i) cs I s n m`.
   That is, the support sets `G_{θ_n'}` and `G_{θ_{n+1}'}` are open, the
   larger one is left `P_J`-invariant, and their difference is the double coset
   `P_J m⁻¹ P_I` (structure in CorrectedGradedInterface).
3. For all `I`, `n`, `hn`, every lift `m` of `w⁻¹`, and every `K` with
   `hK : ∀ x, x ∈ M_I ↔ m⁻¹ x m ∈ M_K`:
   * `(S1)`: for every surviving `J ⊇ K` and every `x ∈ U_I`,
     `m⁻¹ x m ∈ P_J → m⁻¹ x m ∈ U_K`;
   * `(S2)`: for every surviving `J ⊇ K` and every `x ∈ M_J ∩ U_K`,
     `m x m⁻¹ ∈ U_I`;
   * `(D07)`: for every `l ∈ M_I`,

     ```text
     δ_{U_I}(l) · δ_{U_K}(m⁻¹ l m) = δ_{U_I ∩ m U_K m⁻¹}(l) ^ 2,
     ```

     where the moduli are `HaarModulus.closedRestrictCharacter`, the conjugate
     `m⁻¹ l m` is `conjugationEquiv m hK l`, and `U_I ∩ m U_K m⁻¹` is
     `CorrectedFiltration.orbitUnipotentIntersection (U I) (U K) m`, made closed
     and normalized by `M_I` by `isClosed_orbitUnipotentIntersection` and
     `levi_le_normalizer_orbitUnipotentIntersection`.

Facts 2 and 3 are, word for word, the hypotheses `hsupp` of
`CorrectedFiltration.correctedGradedTransitionTarget_of_orbitData`
(CorrectedGradedReduction) and `hS1`, `hS2`, `hD07` of
`CorrectedFiltration.nonempty_orbitJacquetData_of_isLimitOfCompactSubgroups`
(CorrectedOrbitJacquet), specialized to the actual families. Fact 1 is the
instance `[∀ J, CompactSpace (Induction.LeftQuotient (P J))]` of the former.

## The theorem

`rationalCorrectedGradedTransitionStatement_of_inputs` introduces the binders of
the target, applies `H` to the same arguments and destructs the three facts.
Then it proves the remaining assumptions of the generic theorems from the
Library:

* `RationalPoint k G.X` is second countable by
  `reductiveRationalPoint_secondCountable k G hG` (RationalPointSecondCountable).
  With the target's `LocallyCompactSpace` instance, Mathlib's
  `sigmaCompactSpace_of_locallyCompact_secondCountable` makes it σ-compact.
* Every `P_J` is closed by `isClosed_standard_parabolic i ν hStandard hG hi hν J`
  (RationalStandardParabolicTransport). This is `hPc`.
* Every `(h I).projection` is continuous by
  `continuous_standard_projection i ν hStandard hG hi hν I`
  (RationalStandardInductionNonzero). This is `hr`.
* Every `(U I).subgroupOf (P I)` is a limit of compact subgroups by
  `isLimitOfCompactSubgroups_subgroupOf (U I) (P I) (hPc I) (hUc I)`
  (RestrictedLeviTopology), using the target's premise `hUc`.

It registers fact 1 as an instance. Finally it applies
`CorrectedFiltration.correctedGradedTransitionTarget_of_orbitData` at the
universes `u, u, max (u + 1) v`. The arguments are the actual families, `h`,
`hU`, and the other structural terms that appear in the target:

* `standardUnipotent_isUnimodular i ν hU hUc`;
* `standardParabolic_monotone` and `standardUnipotent_antitone`;
* `hM`;
* `isSemidirectDecomposition_in_levi`;
* `rootAssociation`;
* `torusPoints i`.

The remaining arguments are `cs`, `hPc`, fact 2 and the compactness just
proved. The orbit Jacquet data `hD` at a grade come from
`nonempty_orbitJacquetData_of_isLimitOfCompactSubgroups` with fact 3 and `hr`.
The support-category hypothesis of the target is passed to `hD` and is not
used. The result is definitionally the conclusion of
`RationalCorrectedGradedTransitionStatement.{u, v}`.

## Status of the inputs

This module proves none of the three facts. Here is what I found in Library
commits d651c06c and e0b64667:

* Fact 1. `compactSpace_leftQuotient_parabolic` (RationalInductionDualityReduction)
  derives it from `hStandard`, `hG`, `hi`, `hν` and the named proposition
  `BruhatTits.DynamicParabolicQuotientCompactStatement.{u}`. That proposition is
  not proved. The Library reduces it further by
  `dynamicParabolicQuotientCompact_of_flag_and_proper_points` to a flag-quotient
  existence statement and compactness of the points of proper schemes.
* Facts 2 and 3. I found no Library result about `SurvivingSupportHypotheses`
  or `orbitUnipotentIntersection` at the rational points. These names occur only
  in the generic modules CorrectedGradedInterface, CorrectedGradedReduction,
  CorrectedGradedNatural and CorrectedOrbitJacquet.

## Provenance

The definition and the theorem are internal. They are not transcribed from the
literature. The definition packages the explicit hypotheses of the two
published conditional theorems named above, except those the Library already
proves, so that the exact target is reduced to one proposition about rational
points. The mathematical source of the graded transitions is Aubert's erratum
(Trans. AMS 348 (1996), pp. 4688–4690, with the Ban–Jantzen double-coset
correction), as cited in the Markdown of `CorrectedFiltrationStatements` and
`RationalCorrectedFiltrationTargets`.

The three facts are expected to hold for the rational points of a connected
reductive group over a nonarchimedean local field:

* Fact 1 is the standard compactness of `P(k) \ G(k)`.
* Fact 2 is expected from the Bruhat decomposition and from the openness of the
  unions of cells that the length-ordered filtration uses.
* `(S1)`, `(S2)` and `(D07)` are expected from the root-system descriptions of
  the intersections for `w` minimal in `W_J w W_I` (see the Markdown of
  CorrectedOrbitJacquet).
