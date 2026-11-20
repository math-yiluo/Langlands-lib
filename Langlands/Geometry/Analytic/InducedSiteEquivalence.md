# Induction on equivariant quasi-étale sites is an equivalence (from two statements)

Authors: Worker 5254, Worker 933.

This module derives Berkovich's Example 1.2.1(i), quasi-étale case — the
Library statement `InducedSpace.QuasiEtaleSiteEquivalenceStatement` (module
`InducedSiteEquivalenceStatement`) — from two statements taken as
hypotheses:

- `hP : OpenPartitionCoproductStatement.{u, v, z}`: if the underlying space of
  an analytic space is the disjoint union of open subsets, the space is the
  coproduct of the corresponding open domains in `LocalizedCategory`;
- `hR : QuasiEtaleOpenRestrictionStatement.{u, max z v}`: a quasi-étale
  morphism with Hausdorff source restricts to a quasi-étale morphism over an
  open subset of the target (Berkovich 1994, Lemma 3.1(i)).

Neither statement is proved in this module, so the theorems below are
conditional. The first is proved in module `OpenPartitionCoproduct`
(`openPartitionCoproductStatement`). Once the second is proved,
`quasiEtaleSiteEquivalenceStatement_of` applied to the two proofs proves the
target statement. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace`.

Setting: `G : Type z` is a topological group, `H` a subgroup with
`hH : IsOpen (H : Set G)`, `hC : ContinuityStatement.{u, v, z}` and
`hQ : MorphismPropertyStatement.{u, v, z}` are the hypotheses under which the
functor `quasiEtaleSiteInduction hH hC hQ X : Qét(X(H)) ⥤ Qét(X_{G/H}(G))` is
defined (module `InducedEquivariantSite`), and `X : GSpace.{u, max z v, max z v} K H`.

## Declarations

- `essSurj_quasiEtaleSiteInduction hP hR hH hC hQ X`: the functor
  `quasiEtaleSiteInduction hH hC hQ X` is essentially surjective.
- `isEquivalence_quasiEtaleSiteInduction hP hR hH hC hQ X`: the functor
  `quasiEtaleSiteInduction hH hC hQ X` is an equivalence of categories
  (`Functor.IsEquivalence`).
- `quasiEtaleSiteEquivalenceStatement_of hP hR : QuasiEtaleSiteEquivalenceStatement.{u, v, z}`:
  for all `K`, `G`, `H`, `hH`, `hC`, `hQ` and `X`, the functor is an
  equivalence, and a presieve `R` on an object `U` of `Qét(X(H))` is a covering
  exactly when its image under the functor is a covering of the image of `U`.

## Proof

The proof assembles results of other modules:

- faithfulness: the instance `faithful_quasiEtaleSiteInduction` (module
  `InducedSiteFaithful`);
- fullness: `full_quasiEtaleSiteInduction hP hH hC hQ X` (module
  `InducedSiteFull`);
- essential surjectivity: `essSurj_quasiEtaleSiteInduction_of_isIso` (module
  `InducedSiteEssSurj`), whose isomorphism hypothesis — that the comparison
  morphism `lift H (baseInclusion π) : Ind(π⁻¹(X_H)) ⟶ Y` is an isomorphism for
  every `G`-morphism `π : Y ⟶ X_{G/H}` — is `isIso_lift_baseInclusion π hP`
  (module `InducedSiteBaseIso`);
- coverings: `map_quasiEtaleSiteInduction_mem_iff hH hC hQ X U R` (module
  `InducedSiteCoverings`), which uses neither hypothesis.

`Functor.IsEquivalence` is built from its three fields `faithful` (found by
instance search), `full` and `essSurj`. The final theorem introduces the
variables of the statement and returns the pair of the equivalence and the
covering criterion.
