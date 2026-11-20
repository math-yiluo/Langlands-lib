# Induction on equivariant quasi-étale sites preserves and reflects coverings

Author: Worker 933.

This module proves the covering half of Berkovich's Example 1.2.1(i) in the
quasi-étale case. A family of morphisms of `Qét(X(H))` is a covering exactly
when its image under the induction functor
`quasiEtaleSiteInduction hH hC hQ X : Qét(X(H)) ⥤ Qét(X_{G/H}(G))` (module
`InducedEquivariantSite`) is a covering. The other half, that this functor is an
equivalence, is not proved here. The module is a helper for the proof of
`InducedSpace.QuasiEtaleSiteEquivalenceStatement` (module
`InducedSiteEquivalenceStatement`). It imports the helper module
`InducedSpacePoints` (Worker 5254) for the action of induced morphisms on
points. Namespace: `Langlands.Analytic.SaturatedAtlasPresentation`.

## Main result

`InducedSpace.map_quasiEtaleSiteInduction_mem_iff hH hC hQ X U R`. Let `G` be a
topological group and `H` a subgroup with `hH : IsOpen (H : Set G)`. Let `hC`
and `hQ` be proofs of `InducedSpace.ContinuityStatement` and
`InducedSpace.MorphismPropertyStatement`, and `X` an `H`-space. For every
object `U` of `EquivariantQuasiEtaleSite X` and every presieve `R` on `U`:

```
R.map (quasiEtaleSiteInduction hH hC hQ X) ∈
    equivariantQuasiEtalePrecoverage _ ((quasiEtaleSiteInduction hH hC hQ X).obj U)
  ↔ R ∈ equivariantQuasiEtalePrecoverage X U
```

This is exactly the second conjunct of `QuasiEtaleSiteEquivalenceStatement`,
for the given `U` and `R`.

## Auxiliary declarations

- `map_mem_quasiEtalePrecoverage_iff F R`, for a functor `F : C ⥤ QuasiEtaleSite Y`
  and a presieve `R` on `U`. It unfolds `mem_quasiEtalePrecoverage_iff`
  (module `QuasiEtaleSite`) for the image presieve `R.map F`. The condition is:
  every point of `F.obj U` has a neighbourhood that is a finite union of chart
  images `(F.map g).left '' range (chart i)`, where `g : V ⟶ U` lies in `R` and
  `i` is a chart index of `F.obj V`. The arrows of `R.map F` are replaced by the
  arrows of `R`, using the constructor `Presieve.map.of`.
- `InducedSpace.sigma_finite_union_nhds_iff C C'` is a statement about plain
  topological spaces. Let `ι` be nonempty, `C` a family of subsets of `Y`, and
  `C'` a family of subsets of the disjoint union `Σ c : ι, Y`. Assume that the
  copy `Sigma.mk c '' T` of every nonempty `T ∈ C` belongs to `C'` for all `c`,
  and that every member of `C'` is such a copy of a member of `C`. Then every
  point of `Σ c : ι, Y` has a neighbourhood that is a finite union of members of
  `C'` if and only if every point of `Y` has a neighbourhood that is a finite
  union of members of `C`. From left to right, it takes the cover at `⟨c₀, y⟩`
  for some `c₀` and pulls it back along the continuous map `Sigma.mk c₀`. From
  right to left, it pushes the cover at `y` forward along the open map
  `Sigma.mk c`. Empty members are dropped there, because the first hypothesis
  only covers nonempty sets.
- `InducedSpace.exists_range_chart_inducedAction H X k`. The underlying
  presentation of the induced space `inducedAction H X` is the saturation of the
  disjoint union of copies of the presentation of `X`, indexed by `G ⧸ H`
  (modules `InducedAnalyticSpace`, `AtlasDisjointUnion`,
  `SaturatedAffinoidAtlas`). Its charts are the local domains of the disjoint
  union atlas (`IndexedAffinoidAtlas.range_saturatedChart`). A local domain lies
  in one summand `c` and is a local domain of a chart of `X`. By the saturation
  of `X` (`hasAllLocalDomains.exists_chart`) that local domain is itself a chart
  `i` of `X`. Hence the image of every chart `k` of the induced space is
  `Sigma.mk c '' range (chart i)`.
- `InducedSpace.exists_range_chart_inducedAction_eq H X c i hi` is the converse
  for nonempty charts. If chart `i` of `X` has nonempty image, then the whole
  domain of chart `i` in summand `c` is a local domain of the disjoint union atlas
  (`PresentedAffinoidAlgebra.Domain.whole`). Its image is a chart image of the
  induced space and equals `Sigma.mk c '' range (chart i)`
  (`AtlasDisjointUnion.range_chart`). The nonemptiness is needed because the
  disjoint union atlas only uses the nonempty charts of each summand
  (`nonemptyFamily`).
- `InducedSpace.localizedSpaceFunctor_map_forget_map_gSpaceInduction_map_apply`.
  For a morphism `φ : W ⟶ W'` of `H`-spaces, the induced `G`-morphism sends the
  point `⟨c, x⟩` to `⟨c, φ x⟩`. This is `inductionFunctor_map_space_apply`
  (module `InducedSpacePoints`), restated for `gSpaceInduction`.

## Proof of the main result

1. The precoverage `equivariantQuasiEtalePrecoverage` is the pullback of
   `quasiEtalePrecoverage` along `toQuasiEtaleSite`. With
   `Precoverage.comap_comp`, both sides become membership of a mapped presieve
   in a quasi-étale precoverage. On the left the functor is the composite of
   induction and `toQuasiEtaleSite`. On the right it is `toQuasiEtaleSite`. Both
   sides are unfolded by `map_mem_quasiEtalePrecoverage_iff`.
2. The underlying space of the induced object is definitionally the disjoint
   union `Σ c : G ⧸ H` of copies of the underlying space of `U`. The two
   conditions are then the two sides of `sigma_finite_union_nhds_iff`, where `C`
   is the set of chart images of the arrows of `R`. `C'` is the set of chart
   images of the induced arrows. `G ⧸ H` is nonempty because it contains the
   base coset.
3. Hypotheses of the topological lemma. A nonempty chart image
   `g '' range (chart i)` and a coset `c` are given. Then
   `exists_range_chart_inducedAction_eq` gives a chart `k` of the induced object
   with image `Sigma.mk c '' range (chart i)`. The point formula shows that its
   image under the induced arrow is `Sigma.mk c '' (g '' range (chart i))`.
   Conversely, `exists_range_chart_inducedAction` writes the image of any chart
   `k` of an induced object as `Sigma.mk c '' range (chart i)`. The point formula
   again shows that the induced arrow maps it to the copy in summand `c` of the
   chart image `g '' range (chart i)`.

## Original source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`.
§1.1.2 (printed p.2) constructs `X_{G/H}` as a disjoint union of copies of `X`
indexed by `G/H`. §1.2, Example 1.2.1(i) (printed p.3) states that
`X(N) → X_{G/N}(G)` induces an isomorphism of sites `X(N)_qét ⥲ X_{G/N}(G)_qét`.
Berkovich gives no proof. The statement that induction preserves and reflects
coverings is part of that isomorphism of sites. The argument here (coverings of
a disjoint union are checked summand by summand, and the summands are copies of
`U`) is derived for this formalization.
