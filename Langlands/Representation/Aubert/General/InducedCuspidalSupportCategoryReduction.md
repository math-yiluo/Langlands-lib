# Induced inside-Levi cuspidal representations lie in `Alg({K})`: reduction to Renard VI.3.5

Author: Worker 174, Task 5323 (`c79b0cd0-661f-4239-9f65-483d6f319480`), the
proof task of
`Langlands.Aubert.General.RationalPointFamily.RationalInducedCuspidalSupportCategoryStatement`
(Worker 4195's statement in
[InducedCuspidalSupportCategoryStatement](InducedCuspidalSupportCategoryStatement.md)).

Module `Langlands.Representation.Aubert.General.InducedCuspidalSupportCategoryReduction`.

This unit is a **conditional** reduction. It does not prove the target. It
proves that the target follows from the published whole-category cuspidal
splitting `Langlands.CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement`
(Renard VI.3.5) at the carrier universe `max (u + 1) v`, which is itself
unproved in the Library and has its own proof task. Once that splitting is
proved, `rationalInducedCuspidalSupportCategory_of_wholeStatement` applied to it
is a proof of the exact target. The target pair and every pair it imports are
unchanged.

## Entry theorems

In namespace `Langlands.Aubert.General.RationalPointFamily`:

- `rationalInducedCuspidalSupportCategoryOfWholeStatement` is a definition
  whose type is the implication
  `RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
  RationalInducedCuspidalSupportCategoryStatement.{u, v}` (the `defProp` linter
  is disabled for it). Its value is the next theorem; it packages the
  reduction as one declaration.
- `rationalInducedCuspidalSupportCategory_of_wholeStatement` has type
  `RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
  RationalInducedCuspidalSupportCategoryStatement.{u, v}`, with independent
  universes `u` and `v` and no other parameter. It composes the next theorem
  with `rationalCuspidalExtractionInputs_of_wholeStatement` from
  [RationalLeviInductionExclusionFromWhole](RationalLeviInductionExclusionFromWhole.md).
- `rationalInducedCuspidalSupportCategory_of_extractionInputs` has type
  `RationalCuspidalExtractionInputsStatement.{u, v} →
  RationalInducedCuspidalSupportCategoryStatement.{u, v}`. The premise is the
  published conjunction of the actual geometric filtration and the
  proper-standard induction exclusion
  ([RationalCuspidalExtractionInputs](RationalCuspidalExtractionInputs.md)). The
  proof introduces the target's binders in order, installs `hG.isAffineHom`,
  `hi.isSplitSubtorus.mono`, `pointTopology` and `simpleRelativeRootFintype`,
  specializes the premise to the same data and applies the datum-level theorem
  below.
- `inducedCuspidalSupportCategory_of_filtration_exclusion` is the datum-level
  argument. At one displayed datum it assumes the two inputs: an actual point
  Coxeter system `cs` with `RootLengthComparison` and
  `PointInducedJacquetGeometricFiltration … cs`, and
  `PointLeviStandardInductionCuspidalExclusion`. It concludes the target's
  `InducedCuspidalSupportCategoryTarget.{u, u, max (u + 1) v}` for the actual
  standard families, the actual decompositions
  `isSemidirectDecomposition_of_standardCocharacterStatement` and
  `isSemidirectDecomposition_in_levi`, and the actual association
  `rootAssociation i ν hN hZ`.

All rational data are those of the target: every nonarchimedean local field,
every connected reductive group scheme, the actual maximal split torus and
generic cocharacter, the canonical point topology with its locally compact,
nonarchimedean and Hausdorff instances, `hStandard`, `hInter`, `hRoots`, `hN`,
`hZ`, closed radicals and Levis. Representation carriers are in
`max (u + 1) v`. The inside-Levi cuspidal `τ` is arbitrary: it may be
reducible, zero, not admissible, not finitely generated and of infinite length.

## The datum-level argument

Let `K` be a standard subset, `τ` an `IsLeviCuspidal` smooth representation of
`M_K = levi i ν K`, and `π` an irreducible actual subquotient of
`i_K(τ) = (normalizedInductionFunctor (h K) (hU K)).obj τ`.

1. **Minimal cuspidal datum of `π`.** `exists_cuspidal_jacquet_quotient_embedding`
   produces a standard `I` and an irreducible `IsLeviCuspidal` `ρ` on `M_I`
   which is an actual subquotient of `r_I(π)` (it is constructed as a
   quotient) and such that `π` is an actual subquotient of `i_I(ρ)` (it is
   constructed as an injective intertwiner `π → i_I(ρ)`). It uses the published
   `exists_nontrivial_isLeviCuspidal_jacquet` (an index of minimal cardinality
   with nonzero Jacquet module, at which the Jacquet module is inside-Levi
   cuspidal), finite generation of `r_I(π)` from compactness of `P_I \ G`
   (`JacquetFiniteGeneration.finite_of_compactQuotient`,
   `compactSpace_leftQuotient_parabolic`, the unconditional
   `BruhatTits.dynamicParabolicQuotientCompact`), an irreducible quotient
   (`CuspidalEmbedding.exists_irreducible_quotient_of_finite`), preservation of
   cuspidality by quotients (`IsLeviCuspidal.of_surjective`) and actual first
   adjointness with injectivity on the irreducible `π`
   (`CuspidalEmbedding.adjointOfJacquetMap`, `adjointOfJacquetMap_injective`,
   unimodularity from `standardUnipotent_isUnimodular_of_standardCocharacterStatement`).
   This replays the published proof of `rationalCuspidalSeriesExistence`,
   retaining the quotient map, which that theorem does not expose.
2. **Exactness.** The published `isSubquotient_jacquet_induction_of_exact`, with
   actual Jacquet exactness from
   `standardJacquetFunctor_map_isShortExact_of_standardCocharacterStatement`,
   makes `ρ` an actual subquotient of `r_I(i_K τ)`.
3. **Geometric filtration and its grades.** The supplied filtration of
   `r_I(i_K τ)` has grades isomorphic to geometric terms at minimal classes.
   The published `pointCuspidalExtractionGeometry_of_rootComparisons`,
   `pointProperTargetGeometricTermExclusion_of_standardInduction` (fed by the
   exclusion input) and `pointGeometricCuspidalGradeDichotomy_of_geometry_exclusion`
   show that each term either has no irreducible inside-Levi cuspidal
   subquotient (proper source intersection: the term vanishes by cuspidality
   of `τ`; full source and proper target: the term is a proper standard
   induction inside `M_I`) or is actually isomorphic to the conjugate
   `(conjugationFunctor n hn).obj τ` with `rootAssociation K I n`.
   `pointCuspidalJacquetGradedPieces_of_geometricTerms` records this as
   `CuspidalJacquetGradedPieces`. None of these steps assumes `τ` irreducible.
4. **Extraction for a reducible datum.** The generic
   `exists_conjugation_isSubquotient_of_gradedPieces` chooses a grade containing
   `ρ` (`ObjectRepFiltration.exists_smoothGradedObject_subquotient`); it cannot
   be an excluded grade, so `ρ` is an actual subquotient of
   `(conjugationFunctor n hn).obj τ` with `rootAssociation K I n` and the same
   `hn : ∀ x, x ∈ M_I ↔ n⁻¹ x n ∈ M_K`. Unlike the published
   `cuspidalJacquetFactor_of_finiteFiltration`, it needs no irreducibility of
   the inducing datum and concludes a subquotient, not an isomorphism.
5. **Back to an irreducible cuspidal constituent of `τ`.** The generic
   `exists_inducedConjugate_of_conjugation_isSubquotient` sets
   `σ = (conjugationFunctor n⁻¹ _).obj ρ` on `M_K`. Pullback along the actual
   conjugation equivalence preserves subquotients
   (`SmoothRep.IsSubquotient.pullback`), and `conjugationFunctorInvIsoApp`
   identifies the double conjugate of `τ` with `τ`; hence `σ` is an actual
   subquotient of `τ`. It is irreducible
   (`isIrreducible_comp_continuousMulEquiv_iff`) and inside-Levi cuspidal by
   `IsLeviCuspidal.of_isSubquotient`, whose compact-limit premise for the
   restricted radicals comes from
   `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
   and `isLimitOfCompactSubgroups_subgroupOf`. The conjugate of `σ` by
   `(n⁻¹)⁻¹` is identified with `ρ` by `conjugationFunctorInvIsoApp`, and the
   induction functor carries this to an isomorphism `i_I(ρ) ≅ i_I(Ad(n⁻¹⁻¹) σ)`.
6. **Conclusion.** The witness for `IsInSupportCategory` at `π` is the index
   `I`, the point `(n⁻¹)⁻¹` with membership witness
   `conjugationMembership_inv n⁻¹ _`, the association
   `rootAssociation K I (n⁻¹)⁻¹` (rewriting `inv_inv` in step 4's
   association), and `σ`; `π ↪ i_I(ρ)` becomes a subquotient of
   `i_I((conjugationFunctor (n⁻¹)⁻¹ _).obj σ)`.

The elementary point `(n⁻¹)⁻¹` is equal to `n`; it is kept in this form so that
the membership witness and the conjugation isomorphism are the published
composition lemmas of `ConjugationComposition` without further transport.

## Generic lemmas

In namespace `Langlands.Aubert.General`, for arbitrary standard families over
any locally compact nonarchimedean group, with carriers in `max uG uV`:

- `exists_conjugation_isSubquotient_of_gradedPieces`: an irreducible
  inside-Levi cuspidal subquotient of an object with a finite filtration
  satisfying `CuspidalJacquetGradedPieces … I J σ s` is an actual subquotient of
  `(conjugationFunctor n hn).obj σ` for some `n`, `hn` with `IsAssociate I J n`.
- `exists_inducedConjugate_of_conjugation_isSubquotient`: step 5 above, for any
  semidirect family, under the compact-limit premise for the restricted
  radicals of `M_I`.

## Remaining input and ownership

The only hypothesis of the final theorem is
`RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`, whose
proof task is Task 4386 (`4bee987a-093b-4054-bd65-7360168351d2`). The
geometric filtration is proved unconditionally in
[RationalInducedJacquetGeometricFiltration](RationalInducedJacquetGeometricFiltration.md),
and the inside-Levi exclusion is derived from the splitting in
[RationalLeviInductionExclusionFromWhole](RationalLeviInductionExclusionFromWhole.md).
This reduction does not use `RationalCuspidalJacquetFactorExtractionStatement`,
`RationalCuspidalSupportAssociationStatement` or
`RationalCuspidalInducedEmbeddingStatement`.

## Source and provenance

D. Renard, *Représentations des groupes réductifs p-adiques*, version of
9 July 2026, `renard-2026-representations-groupes-reductifs-padiques`
(SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`),
proof of Théorème VI.7.2, final paragraph of printed p.183 / PDF p.189. There,
a composition factor `(σ, E)` of `i^G_P(W_D)` has `r^G_P(σ, E)` a subquotient of
`r^G_P i^G_P(W_D)` by exactness, and the filtration of Proposition VI.5.3 (iii)
(printed p.173 / PDF p.179) by the conjugates `w(W_D)` places its cuspidal
support in the component of `D`. The implemented argument differs in two
documented ways. It applies the Jacquet functor along the index `I` of a
minimal cuspidal datum of `π`, not along `P_K`, so that the irreducible
cuspidal quotient `ρ` of `r_I(π)` gives `π ↪ i_I(ρ)` by Frobenius reciprocity.
It then uses the geometric filtration of `r_I i_K(τ)` (Renard VI.5.1) for an
arbitrary inducing `τ`, where proper target terms are removed by Renard's
Lemme VI.5.2 inside `M_I` (the exclusion input) rather than by VI.5.3 (ii). The
grouping by association classes of cuspidal Levis is internal (derived), as
explained in the target's Markdown.
