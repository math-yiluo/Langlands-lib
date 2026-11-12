# Rational rank-one Jacquet pattern from maximal Jacquet detection

Author: Worker 3917.

This module reduces the exact host target
`RationalRankOneJacquetModulesStatement.{u, v}` of
[RationalCorollaryTargets](RationalCorollaryTargets.md) to one
representation-theoretic input: the published proposition
`RationalMaximalCuspidalJacquetDetectionStatement.{u, v}` of
[RationalRankOneLengthInputsStatement](RationalRankOneLengthInputsStatement.md).
Through the published reduction of that proposition to factor extraction, it
also reduces the host target to
`RationalCuspidalJacquetFactorExtractionStatement.{u, v}` of
[RationalCuspidalJacquetFactorTarget](RationalCuspidalJacquetFactorTarget.md).
The module proves implications only. Neither the detection proposition nor the
extraction proposition is proved here, so the host target is not proved here.

The earlier reduction in
[RationalRankOneJacquetReduction](RationalRankOneJacquetReduction.md) needed
three inputs: the length-two proposition `RationalRankOneLengthTwoStatement`,
support-category detection (or extraction), and the geometric proposition
`RationalRankOneGeometricJacquetStatement`. The geometric proposition is now
proved by `rationalRankOneGeometricJacquet` in
[RationalRankOneGeometricJacquetProof](RationalRankOneGeometricJacquetProof.md).
This module derives the length-two conclusion and the nonvanishing of both
constituents' Jacquet modules from maximal detection and that geometric
theorem. It therefore needs neither `RationalRankOneLengthTwoStatement` nor
`RationalMaximalCuspidalJacquetBudgetStatement`. That budget proposition
quantifies over every maximal `J`. The host target only concerns a maximal `J`
normalized by the lift `n`, and for such `J` the geometric theorem computes the
budget.

## The statement `RationalRankOneJacquetModulesFromDetectionStatement`

```
RationalMaximalCuspidalJacquetDetectionStatement.{u, v} →
  RationalRankOneJacquetModulesStatement.{u, v}
```

Both sides are published propositions with independent universe parameters
`u` (field) and `v` (carrier, at universe `max (u + 1) v`). The implication
adds no premise and changes neither proposition.

Provenance: derived. This is an internal step on the proof route of the host
target. It introduces no new mathematical assertion from the literature. Its
inputs and its conclusion are already-published propositions, whose sources are
documented in their own Markdown. The underlying source argument is Aubert's
proof of Corollaire 1.10(b) (Trans. Amer. Math. Soc. 347 (1995), printed
p. 2183), as documented in
[RationalRankOneJacquetReduction](RationalRankOneJacquetReduction.md).

## The proof `rationalRankOneJacquetModules_of_maximalDetection`

The proof introduces exactly the binders of the host target: the nonarchimedean
local field `k`, the connected reductive `G`, the maximal split torus `i`, the
canonical `pointTopology` and its instance premises, the generic cocharacter
`ν`, the structural statements, the closed radicals and Levis, the
`simpleRelativeRootFintype` enumeration with classical decidable equality, the
Coxeter data and comparison premises, a maximal standard `J`, a finite-length
`σ` with irreducibility, cuspidality (`IsCorollaryLeviCuspidal`) and
reducibility of `i_J σ`, a lift `n` with `QuotientGroup.mk n = longestRep actual
J`, and a self-normalization witness `hself`. Here `i_J` and `r_K` are the
actual `normalizedInductionFunctor` and `jacquetFunctor` of the decompositions
`isSemidirectDecomposition_of_standardCocharacterStatement`, and every radical is
a limit of compact subgroups by
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.

1. **Geometry.** The published theorem `rationalRankOneGeometricJacquet`,
   applied to the same data, `n`, `hn` and `hself`, gives the actual short exact
   sequence `0 → Ad(n⁻¹) σ → r_J(i_J σ) → σ → 0`
   (`HasRankOneJacquetMiddleSequence`) and `IsZero (r_K(i_J σ))` for every
   `K ≠ univ`, `K ≠ J`.
2. **Detection at `J`.** Write `J = univ.erase α`. The detection input gives,
   for every actual irreducible subquotient `D` of `i_J σ`, a label `β` with
   `r_(univ.erase β) D` nontrivial. If `β ≠ α`, then `univ.erase β` is
   different from `J` (by `Finset.erase_inj`) and from `univ`
   (`IsMaximalStandard.ne_univ`). So `r_(univ.erase β)(i_J σ)` is zero by
   step 1. The published `jacquet_subsingleton_of_isSubquotient` (exactness of
   the actual Jacquet functor on subquotients) then makes
   `r_(univ.erase β) D` zero, a contradiction. Hence `β = α`, and `r_J D` is
   nontrivial.
3. **Budget at `J`.** The sum over all labels `β` of the actual composition
   lengths `repLength (r_(univ.erase β)(i_J σ))` is at most `2` in `ℕ∞`. By
   `Finset.sum_eq_single`, every term with `β ≠ α` is `0`: its Jacquet module is
   zero by step 1, and `repLength_eq_zero_iff` applies. The term at `α` is the
   length of the middle of the exact sequence of step 1. By
   `repLength_eq_add_of_exact` it is the length of `Ad(n⁻¹) σ` plus that of
   `σ`. Both are irreducible, hence of length one (`repLength_eq_one_iff`).
   Irreducibility of `Ad(n⁻¹) σ` is transported from `σ` along the continuous
   group isomorphism `conjugationEquiv` by
   `isIrreducible_comp_continuousMulEquiv_iff`.
4. **Length two.** `i_J σ` is nonzero by `rationalStandardInductionNonzero`,
   because the irreducible `σ` is nonzero. The published generic criterion
   `repLength_le_two_of_jacquetFamily`, applied to the family of the maximal
   proper standard Jacquet functors `r_(univ.erase β)`, to the budget of step 3
   and to the detection of step 2, gives `repLength (i_J σ) ≤ 2`. Since `i_J σ`
   is reducible, the published `exists_hasTwoConstituents_of_length_le_two`
   returns actual finite-length objects `A`, `B` with
   `HasTwoConstituents (i_J σ) A B`.
5. **Pattern.** By `HasTwoConstituents.isSubquotient`, `A` and `B` are actual
   irreducible subquotients of `i_J σ`. So step 2 shows that `r_J A` and `r_J B`
   are nontrivial. The published `exists_rankOneJacquetPattern_of_exact_data`,
   applied to these nonvanishings, the exact sequence and vanishing of step 1,
   and the same `n` and `hself`, returns the ordered pair `(ρ₊, ρ₋)` with
   `HasTwoConstituents (i_J σ) ρ₊ ρ₋` and `RankOneJacquetPattern`. This is the
   witness the host target asks for.

The lift `n` and the witness `hself` supplied by the host target are passed
unchanged. So the actual isomorphisms `r_J ρ₊ ≅ σ` and `r_J ρ₋ ≅ Ad(n⁻¹) σ`
hold for that lift. The proof does not compare Grothendieck classes. Every
length is an actual module length, and every isomorphism is an actual
isomorphism of smooth representations.

`rationalRankOneJacquetModulesFromDetection` records the named implication.

## The extraction variant `rationalRankOneJacquetModules_of_extraction`

```
RationalCuspidalJacquetFactorExtractionStatement.{u, v} →
  RationalRankOneJacquetModulesStatement.{u, v}
```

It composes the main theorem with the published
`rationalMaximalCuspidalJacquetDetectionFromExtraction` of
[RationalMaximalCuspidalDetectionProof](RationalMaximalCuspidalDetectionProof.md).
Once the extraction proposition is proved (its proof task is
`e6add7c5-44c5-45ea-afe9-7f48c98fb927`), this theorem applied to that proof
proves the host target.

## Dependencies

Published declarations used directly: `rationalRankOneGeometricJacquet`,
`rationalMaximalCuspidalJacquetDetectionFromExtraction`,
`repLength_le_two_of_jacquetFamily`, `exists_hasTwoConstituents_of_length_le_two`,
`HasTwoConstituents.isSubquotient`, `exists_rankOneJacquetPattern_of_exact_data`,
`jacquet_subsingleton_of_isSubquotient`, `SmoothRep.isZero_iff_subsingleton_carrier`,
`rationalStandardInductionNonzero`,
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`,
`isIrreducible_comp_continuousMulEquiv_iff`, `conjugationEquiv`,
`IsMaximalStandard.ne_univ`, `repLength_eq_add_of_exact`,
`repLength_eq_one_iff` and `repLength_eq_zero_iff`, with Mathlib's
`Finset.erase_inj`, `Finset.sum_eq_single` and `IsSimpleModule.nontrivial`.

Transitive dependencies of note:

- The geometric lemma enters only through the proved theorem
  `rationalRankOneGeometricJacquet`. Its proof constructs the actual geometric
  filtration (`rationalMaximalSourceGeometricFiltration`) and is documented in
  [RationalRankOneGeometricJacquetProof](RationalRankOneGeometricJacquetProof.md).
- Cuspidal support (Renard VI.5.2–VI.5.4 in extraction form) enters only through
  the unproved premise `RationalMaximalCuspidalJacquetDetectionStatement`, or in
  the variant the unproved premise `RationalCuspidalJacquetFactorExtractionStatement`.
  The variant also uses `rationalWeylComparison` through
  `rationalMaximalCuspidalJacquetDetectionFromExtraction`.
- Length bounds use actual module length and the exactness of the actual
  Jacquet functors, through `repLength_le_two_of_jacquetFamily` and
  `jacquet_subsingleton_of_isSubquotient`.
- No instance of Langlands classification, character independence or
  adjointness is invoked by this module.

## What remains

The host target is proved as soon as either
`RationalMaximalCuspidalJacquetDetectionStatement.{u, v}` or
`RationalCuspidalJacquetFactorExtractionStatement.{u, v}` is proved. An empty
simple-root type has no maximal standard subset, so the host target is then
vacuous; no nonemptiness premise is added.
