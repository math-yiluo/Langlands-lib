# Proof: induction on equivariant quasi-étale sites is an equivalence

Authors: Worker 5254, Worker 933.

This module proves the Library statement
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace.QuasiEtaleSiteEquivalenceStatement`
(module `InducedSiteEquivalenceStatement`), Berkovich's Example 1.2.1(i) in
the quasi-étale case. It contains one theorem and no new definitions.

## Main result

`InducedSpace.quasiEtaleSiteEquivalenceStatement : QuasiEtaleSiteEquivalenceStatement.{u, v, z}`.

Let `K : Type u` be a complete ultrametric normed field. Let `G : Type z` be a
topological group, `H` a subgroup with `hH : IsOpen (H : Set G)`, and
`X : GSpace.{u, max z v, max z v} K H` an `H`-space. Let `hC` and `hQ` be
proofs of `InducedSpace.ContinuityStatement.{u, v, z}` and
`InducedSpace.MorphismPropertyStatement.{u, v, z}`. The functor
`quasiEtaleSiteInduction hH hC hQ X : Qét(X(H)) ⥤ Qét(X_{G/H}(G))` is defined
only under these two hypotheses (module `InducedEquivariantSite`). The theorem
proves:

1. the functor is an equivalence of categories (`Functor.IsEquivalence`);
2. for every object `U` of `Qét(X(H))` and every presieve `R` on `U`, the image
   `R.map (quasiEtaleSiteInduction hH hC hQ X)` is a covering of the image of
   `U` in `equivariantQuasiEtalePrecoverage` exactly when `R` is a covering of
   `U`.

As in the statement, `hC` and `hQ` remain universally quantified hypotheses.
They are needed only to define the functor. The theorem does not prove them.

## Proof

The theorem is the term

```
quasiEtaleSiteEquivalenceStatement_of openPartitionCoproductStatement.{u, v, z}
  quasiEtaleOpenRestriction.{u, max z v}
```

It instantiates the conditional assembly `quasiEtaleSiteEquivalenceStatement_of`
(module `InducedSiteEquivalence`) with proofs of its two hypotheses:

- `openPartitionCoproductStatement : OpenPartitionCoproductStatement.{u, v, z}`
  (module `OpenPartitionCoproduct`). An analytic space whose underlying space
  is a disjoint union of open subsets is the coproduct of the corresponding
  open domains in `LocalizedCategory`.
- `quasiEtaleOpenRestriction : QuasiEtaleOpenRestrictionStatement.{u, max z v}`
  (module `QuasiEtaleOpenRestrictionProof`, Worker 912). A quasi-étale
  morphism with Hausdorff source restricts to a quasi-étale morphism
  `f⁻¹(V) → V` over every open subset `V` of the target (the open-domain case
  of Berkovich 1994, Lemma 3.1(i)). It is used at the universes
  `{u, max z v}` of the spaces in `GSpace.{u, max z v, max z v} K H`.

The conditional assembly combines the following published results:

- faithfulness: the instance `faithful_quasiEtaleSiteInduction` (module
  `InducedSiteFaithful`). A copy inclusion into the induced space is split by
  the fold morphism, so it can be cancelled from induced morphisms.
- fullness: `full_quasiEtaleSiteInduction` (module `InducedSiteFull`), from the
  open-partition coproduct theorem. A `G`-morphism `ψ` of induced spaces over
  the base preserves the coset of every point. So `ψ` maps the copy indexed by
  `H` into the corresponding copy of the target. Folding that copy back onto
  the `H`-space (module `InducedSiteFold`, which uses the open-partition
  coproduct theorem) gives an `H`-morphism. Its induction is `ψ` by the
  universal property of induction.
- essential surjectivity: `essSurj_quasiEtaleSiteInduction_of_isIso` (module
  `InducedSiteEssSurj`). A quasi-étale `G`-space `π : Y → X_{G/H}` has the
  `H`-space `π⁻¹(X_H)` over `X` (module `InducedSiteBase`). Its structure
  morphism is quasi-étale by the open-restriction theorem, since it is the
  restriction of `π` over the open copy `X_H`. The comparison morphism
  `lift H (baseInclusion π) : Ind(π⁻¹(X_H)) → Y` is an isomorphism by
  `isIso_lift_baseInclusion` (module `InducedSiteBaseIso`). There the
  open-partition coproduct theorem identifies `Y` with the disjoint union of
  the translates `π⁻¹(X_c)` of `π⁻¹(X_H)`.
- coverings: `map_quasiEtaleSiteInduction_mem_iff` (module
  `InducedSiteCoverings`), which uses neither hypothesis. The underlying space
  of an induced object is the disjoint union of copies of the underlying space
  of `U`, indexed by `G ⧸ H`. The chart images of the induced arrows are the
  copies of the chart images of the arrows of `R`. So the neighbourhood
  condition defining quasi-étale coverings holds on the disjoint union exactly
  when it holds on `U`.

The resulting theorem uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Original source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, Example 1.2.1(i), printed p.3. Berkovich states the example without
proof. The Library statement covers only the quasi-étale case, with induction
as the functor. This proof follows the route sketched in
`InducedSiteEquivalenceStatement.md`. A quasi-inverse takes the preimage of
the copy indexed by `H`, morphisms are determined copy by copy, and coverings
are local on the open copies. The open-restriction input is Berkovich,
*Vanishing cycles for formal schemes*, Invent. Math. 115 (1994), Lemma 3.1(i),
printed p.544 (registered as `berkovich-1994-vanishing-cycles-formal-schemes`).

## Scope

Neither the étale case of Example 1.2.1(i) nor the induced isomorphism of
topoi is proved here.
