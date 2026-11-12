# Support stability under induction after Jacquet restriction, by blocks

Worker 4197 wrote this derived internal reduction for the exact proof task of
`Langlands.Aubert.General.RationalPointFamily.RationalSupportCategoryInductionJacquetStatement`.
It does not prove that target. It proves that the target follows from three
other published propositions, which stay separate proof obligations:

1. `RationalSupportCategoryDecompositionStatement.{u, v}`, the actual support
   decomposition (Renard, Théorème VI.7.2), from
   [RationalSupportCategoryTargets](RationalSupportCategoryTargets.md);
2. `CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`,
   the closed two-factor cuspidal decomposition of the whole smooth category
   (Renard, Théorème VI.3.5), from
   [RationalWholeCuspidalDecompositionStatement](../../CuspidalSupport/RationalWholeCuspidalDecompositionStatement.md);
3. `RationalCuspidalSupportAssociationStatement.{u, v}`, association of actual
   cuspidal data (Renard, Théorème VI.5.4), from
   [RationalSupportCategoryTargets](RationalSupportCategoryTargets.md).

## Entry statement

`RationalSupportCategoryInductionJacquetReductionStatement.{u, v}` is the
proposition (1) → (2) → (3) → `RationalSupportCategoryInductionJacquetStatement.{u, v}`.
The theorem `rationalSupportCategoryInductionJacquetReduction` proves it. All
four propositions are used unchanged, at independent universes `u` and `v`.
The whole-category proposition takes its representation carrier universe as its
second universe parameter. Here that parameter is `max (u + 1) v`, the carrier
universe of the target. No other premise is added. Ambient quotient compactness,
unimodularity, compact limits, the intrinsic Levi root systems, the minimal
cuspidal Levi Jacquet module, Jacquet restriction in stages, the
root-association laws, conjugation of cuspidality and association invariance
all come from published Library results, as described below. The conclusion
covers every smooth `E` in `Alg({I})`, with no finite-length, admissibility or
`K_0` restriction.

The proof composes two theorems of this module.

`rationalLeviJacquetSplitting_of_wholeDecomposition` proves
`RationalLeviJacquetCuspidalRemainderSplittingStatement.{u, v}` (from
`Langlands.Representation.CuspidalSupport.RationalFiniteCuspidalEmbeddingReduction`)
from the whole-category proposition at the same universes. That statement asks
for the literal cuspidal/remainder splitting, inside every standard Levi, of
every actual normalized Jacquet module. The proof introduces the binders of the
splitting statement and installs the same instances as below. For each smooth
`A` and standard `L` it applies Worker 1570's published
`hasLeviCuspidalRemainderSplitting_of_wholeStatement`
([RationalLeviSplittingFromWhole](../../CuspidalSupport/RationalLeviSplittingFromWhole.md))
to the Jacquet module of `A`. That theorem keeps one explicit input, a relative
root system for the intrinsic maximal split torus of the standard Levi scheme.
This module supplies it with the published
`Langlands.GroupScheme.relativeRootSystem`. The required facts are connected
reductivity of the Levi scheme (`standardLeviScheme_isConnectedReductive` with
the published `Langlands.GroupScheme.dynamicCentralizerReductive`) and
maximality of its torus factor
(`IsMaximalSplitTorus.isMaximalSplitTorus_standardLeviTorusFactor`).

The theorem
`rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association`
states the implication with the splitting statement at carrier universe
`max (u + 1) v` in place of (2). This form is also usable if the splitting is
proved by another route. It introduces every binder of the target and installs
the target's instances: `hG.isAffineHom`, `hi.isSplitSubtorus.mono`,
`pointTopology` and `simpleRelativeRootFintype`. It then applies the generic
block theorem below. Its arguments are as follows.

* Ambient compactness of `P_K \ G` is
  `compactSpace_leftQuotient_parabolic` applied to the published
  `BruhatTits.dynamicParabolicQuotientCompact`.
* Unimodularity of `U_K` is
  `standardUnipotent_isUnimodular_of_standardCocharacterStatement`.
* The inside-Levi compact limits are
  `standardLeviUnipotent_isLimitOfCompactSubgroups`, applied to
  `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.
* The decomposition, the splitting and the association premises are
  specialized to the displayed data.
* The minimal factorization is the generic
  `exists_cuspidal_factorization_of_jacquet_map_of_stages`, instantiated with
  `levi_le_of_subset`, the compact limits above,
  `exists_nonzero_cuspidal_leviJacquet_of_nontrivial` (below), and
  `standardJacquetStagesIso_of_standardCocharacterStatement`.
* Conjugation of cuspidality is `isLeviCuspidal_conjugation`.
* Composition and inversion of associations are `rootAssociation_mul` and
  `rootAssociation_inv`.
* Association invariance is the published theorem
  `rationalSupportCategoryAssociationInvariance`.

## Generic block argument

The generic theorem
`Langlands.Aubert.General.supportCategoryInductionJacquet_of_decomposition_and_splitting`
proves `SupportCategoryInductionJacquetTarget` from
[SupportCategoryStatements](SupportCategoryStatements.md) for arbitrary families
`P M U` of subgroups indexed by `Finset κ` of a locally compact nonarchimedean
group. It has independent universes `uI`, `uG`, `uV`. Its explicit inputs are:

1. compactness of every `P_K \ G`;
2. `IsUnimodularModulus (U K) (hU K)` for every `K`;
3. for each `L` and `J : Finset L`, `(U (leviIndex L J)).subgroupOf (M L)` is a
   limit of compact subgroups;
4. `SupportCategoryDecompositionTarget`;
5. for every smooth `X` and every `L`, `HasLeviCuspidalRemainderSplitting` of
   `r_L(X)`;
6. a minimal cuspidal factorization: every nonzero actual map
   `r_K(A) → r_K(B)` gives an index `L`, an `IsLeviCuspidal` representation
   `W` of `M_L`, and nonzero actual maps `r_L(A) → W` and `W → r_L(B)`;
7. `CuspidalSupportAssociationTarget`;
8. conjugation by an association representative preserves `IsLeviCuspidal`;
9. composition and inversion of association representatives;
10. `SupportCategoryAssociationInvarianceTarget`.

Proof. Let `E ∈ Alg({I})` and `F = i_K r_K E`. Input 4 writes `F` as an
internal direct sum of subrepresentations `S_J ∈ Alg({J})`. Fix `J`. If `S_J`
is a subsingleton, then `isInSupportCategory_of_subsingleton` applies: it has
no irreducible subquotient. Otherwise the inclusion `S_J → i_K(r_K E)` is
nonzero. `FirstAdjointness.equiv` turns it into a nonzero map
`φ : r_K(S_J) → r_K(E)`. Input 6 gives `L`, a cuspidal `W`, and nonzero maps
`q : r_L(S_J) → W` and `j : W → r_L(E)`.

* `exists_association_of_cuspidal_jacquet_map`, applied to `S_J ∈ Alg({J})`
  and `q`, gives an association `J → L` by some `m₁`, with the Levi membership
  equivalence at the same point.
* `HasCuspidalRemainderSplitting.exists_projection`, applied to input 5 for
  `E` and `L`, gives a cuspidal `C` and a map `p : r_L(E) → C` that detects
  every map from a cuspidal object. So `p ∘ j ≠ 0` and `p ≠ 0`.
* The same lemma, applied to `E ∈ Alg({I})` and `p`, gives an association
  `I → L` by some `m₂`.

Inversion and composition give an association `J → I` by `m₂⁻¹ * m₁`.
`conjugationMembership_mul` and `conjugationMembership_inv` give the
membership equivalence. Input 10 then places `S_J` in `Alg({I})`. The internal
direct sum gives `⨆ J, S_J = ⊤`. `IsInSupportCategory.iSup` places the top
subrepresentation in `Alg({I})`. `F` is its quotient under the subtype map,
so `IsInSupportCategory.of_isSubquotient` concludes.

### Helpers

* `exists_common_irreducible_of_jacquet_map`: a nonzero
  `s : r(A) → σ` gives a nonzero `f : A → i(σ)` by `FirstAdjointness.equiv`.
  The image of `f` is nonzero, and its irreducible subquotient from
  `SmoothRep.RenardIrreducibleExistence.exists_irreducible_subquotient` is a
  common irreducible subquotient of `A` and `i(σ)`.
* `exists_association_of_cuspidal_jacquet_map` uses inputs 1, 2, 3, 7, 8 and
  composition. Suppose `X ∈ Alg({I})`, `C` is cuspidal on `M_L`, and
  `q : r_L(X) → C` is nonzero. The proof picks a vector `x` of `X` whose
  Jacquet class has nonzero image, and lets `A` be the cyclic subrepresentation
  generated by `x`. `A` is finitely generated over `ℂ[G]`, so
  `JacquetFiniteGeneration.finite_of_compactQuotient` makes `r_L(A)` finitely
  generated. The image of `r_L(A) → C` is nonzero, finitely generated and
  cuspidal (`IsLeviCuspidal.of_isSubquotient`, using input 3). Hence it has an
  irreducible quotient `ρ`
  (`JacquetCommonConstituent.exists_irreducible_quotient_of_moduleFinite`),
  and `ρ` is cuspidal by `IsLeviCuspidal.of_surjective`. The previous helper
  gives an irreducible `π` common to `A` (hence to `X`) and `i_L(ρ)`.
  Membership of `X` in `Alg({I})` presents `π` as a subquotient of
  `i_J(n·σ)`, with `σ` irreducible cuspidal on `M_I` and `n` an association
  `I → J`. Input 8 makes `n·σ` cuspidal, and the conjugate is irreducible by
  `isIrreducible_comp_continuousMulEquiv_iff`. Input 7, applied to the data
  `(J, n·σ)` and `(L, ρ)`, gives an association `J → L` by some `m`.
  Composition gives `I → L` by `m * n`, and `conjugationMembership_mul` gives
  the membership equivalence.
* `leviNormalizedJacquetFunctor_map_surjective` and
  `leviNormalizedJacquetFunctor_map_injective`: Levi normalized Jacquet
  restriction preserves surjective actual maps, and injective actual maps when
  `N.subgroupOf M` is a limit of compact subgroups. These are
  `Jacquet.Localization.map_surjective` and
  `Jacquet.Localization.map_injective_of_smooth` with the trivial character.
* `exists_cuspidal_factorization_of_jacquet_map_of_stages` proves input 6 from
  three hypotheses: the Levi inclusions, the inside-Levi compact limits, and
  two Levi-level facts. The first is that every nontrivial representation of
  `M_K` has, for some `I : Finset K`, a nontrivial `IsLeviCuspidal` Levi
  Jacquet module along `leviIndex K I`. The second is an isomorphism
  `r_K ⋙ r^{M_K}_{leviIndex K I} ≅ r_{leviIndex K I}`. For nonzero `φ`, let
  `Y` be its image and `W = r^{M_K}_L(Y)` such a cuspidal Levi Jacquet module.
  The induced map `r^{M_K}_L(r_K A) → W` is surjective, and
  `W → r^{M_K}_L(r_K B)` is injective. Composing with the stages isomorphism
  gives the two nonzero maps.
* The rational
  `RationalPointFamily.exists_nonzero_cuspidal_leviJacquet_of_nontrivial`
  states the first Levi-level fact for the actual standard Levis. Its proof is
  the minimal-index argument of the published
  `exists_nonzero_cuspidal_leviJacquet`
  ([RationalLeviCuspidalJacquet](RationalLeviCuspidalJacquet.md)), which uses
  irreducibility only to obtain a nonzero vector. The index set of minimal
  cardinality with nonzero Jacquet module exists because the full index has a
  trivial radical. The published relation-span and coinvariant-transport
  lemmas `CuspidalEmbedding.mem_relations_of_subsingleton`,
  `CuspidalEmbedding.closedNormalizerCharacter_eq_one_of_compactLimit` and
  `CuspidalEmbedding.subgroupOfPullbackCoinvariantsEquiv` then prove
  cuspidality.
* `hom_hom_injective_of_iso`, `hom_inv_surjective_of_iso`,
  `hom_ne_zero_of_surjective` and `hom_ne_zero_of_injective` are elementary
  facts about actual intertwiners.

## Dependencies and provenance

This is derived internal content. It makes no new assertion from the
literature. The route follows the block structure in Renard, Théorème VI.7.2
(printed p.182) and Proposition VI.7.3 (printed p.185), in
*Représentations des groupes réductifs p-adiques*, registered as
`renard-2026-representations-groupes-reductifs-padiques`. The retained
premise (2) is Théorème VI.3.5 (printed pp.146–147), and only its closed
whole-category statement is used. It uses no
Langlands classification, character independence or geometric lemma. Its
adjointness ingredient is `Langlands.Aubert.General.FirstAdjointness.equiv`
for the actual normalized functors, with its `IsUnimodularModulus` hypothesis
discharged on the rational families. Finite generation of Jacquet modules
uses `JacquetFiniteGeneration.finite_of_compactQuotient` under the ambient
quotient compactness supplied above.

Some arguments adapt published Library proofs:

* the cyclic-module and coatom-quotient steps adapt Worker 158's
  [JacquetCommonConstituent](JacquetCommonConstituent.md), and the
  association step adapts the associated-subset witness of
  [JacquetSupportVanishingReduction](JacquetSupportVanishingReduction.md);
* the minimal-index step adapts
  [RationalLeviCuspidalJacquet](RationalLeviCuspidalJacquet.md), itself
  adapted from Worker 379's `RationalCuspidalEmbeddingProof`;
* the rational adapter follows
  [RationalJacquetVanishingFromDynamicCompactness](RationalJacquetVanishingFromDynamicCompactness.md).

The three retained premises are not proved here and are not replaced by
weaker statements. Association invariance is not a premise, because it is
imported as the published theorem `rationalSupportCategoryAssociationInvariance`.
