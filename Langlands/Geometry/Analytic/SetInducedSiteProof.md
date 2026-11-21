# Berkovich's functor `Σ ↦ X_Σ(G)` is representably flat and continuous

Author: Worker 384.

This module proves `SetInducedSpace.MorphismOfSitesStatement` (module
`SetInducedSiteStatement`). The final theorem is

`morphismOfSitesStatement : MorphismOfSitesStatement.{u, v, z}`.

For every complete ultrametric normed field `K`, topological group `G`, proofs
`hC : ContinuityStatement` and `hD : SigmaDescStatement` and `G`-space `X`,
the functors `quasiEtaleSiteFunctor hC X hD` and `etaleSiteFunctor hC X hD`
from `P(G)` are representably flat and continuous for the topology of `P(G)`
and the equivariant quasi-étale (resp. étale) topology of `X`. The proof uses
`hC` and `hD` only to form the functors `γ`. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace`.

The geometric input is module `CopiesOverHom`, which also provides the point
maps of disjoint unions used below (`localizedSpaceFunctor_map_localizedSigmaCofan_inj`, `sigma_map_apply`, the
index map `index` with `isLocallyConstant_index` and `index_comp`). It proves
that morphisms over `X` into a disjoint union of copies of `X`
correspond to locally constant index maps (`copiesOverHom_ext`,
`exists_copiesOverHom`). The continuity criterion for flat functors is
module `FlatPrecoverageCoverPreserving`.

## Points of the spaces `X_S`

For an action `X` of `G` on an analytic space and `G`-sets `S`, `T`
(module `SetInducedSpace`):

- `mapHom_apply`: `mapHom X f` sends `⟨s, x⟩` to `⟨f s, x⟩`;
- `actionMap_apply`: `actionMap X S g` sends `⟨s, x⟩` to `⟨g • s, (X.ρ g) x⟩`;
- `index_comp_mapHom`, `index_comp_actionMap`: the index of
  `φ ≫ mapHom X f` is `f` of the index of `φ`, and the index of
  `φ ≫ actionMap X S g` is `g •` the index of `φ`.

## Discrete `G`-sets

Constructions in `P(G)` (module `DiscreteGSetSite`), in the namespace
`DiscreteGSetConstructions`: `homOfGMap` (the morphism given by a `G`-map),
`hom_ext`, the one-point `G`-set `point`, the product `prod S T` of two
discrete `G`-sets, and the equalizer `equalizer f f'`, the sub-`G`-set
`eqLocus f f'` where two morphisms agree. In each case the stabilizers are
open: they are `G`, intersections of two stabilizers, and stabilizers of
elements of `S`, respectively.

## Morphisms over `X` into `X_S`

`copiesHom_ext` and `exists_copiesHom` restate `copiesOverHom_ext` and
`exists_copiesOverHom` (module `CopiesOverHom`) for `copies X S` and the
codiagonal `projectionHom X S`.

For a topological group `G`, a `G`-space `X` and `Y` an object of the
category `Over X` of `G`-spaces over `X`, a morphism
`φ : Y ⟶ (gSpaceOverFunctor hC X).obj S` has the index map
`gIndex hC φ`, the index of its underlying morphism of analytic spaces.

- `gHom_w`: the underlying morphism lies over the structure morphism of `Y`.
- `isLocallyConstant_gIndex`, `gIndex_comp_map` (the index of
  `φ ≫ γ(f)` is `f ∘ gIndex φ`) and `gIndex_smul` (the index map is
  `G`-equivariant, because `φ` commutes with the actions).
- `gHom_ext`: two such morphisms with the same index map are equal, by the
  uniqueness result `copiesHom_ext`.
- `exists_gHom`: every locally constant `G`-equivariant map `c` from the
  points of `Y` to `S` is the index map of such a morphism. The existence
  result `exists_copiesHom` gives a morphism `m` of analytic spaces over `X`. It commutes
  with the actions by `copiesHom_ext`: `ρ_Y(g) ≫ m` and
  `m ≫ actionMap g` both lie over `ρ_Y(g) ≫ (Y → X)`, and both have index map
  `y ↦ g • c y` by equivariance of `c`.
- `isCofiltered_structuredArrow`: for every `Y`, the category
  `StructuredArrow Y (gSpaceOverFunctor hC X)` is cofiltered:
  - nonempty: the morphism to `X_{pt}` given by the constant index map;
  - cones over two objects `Y → X_S`, `Y → X_T`: the morphism to
    `X_{S × T}` with the pair of index maps, and the two projections;
  - cones over two parallel morphisms `f, f' : S ⟶ T` under `Y → X_S`: the
    index map of `Y → X_S` takes values in the equalizer of `f` and `f'`,
    and gives a morphism to `X_{equalizer f f'}`; the inclusion of the
    equalizer equalizes `f` and `f'`.
  All commutativity conditions are checked by `gHom_ext` on index maps.
- `representablyFlat_gSpaceOverFunctor`: hence `gSpaceOverFunctor hC X` is
  representably flat.

## Flatness and continuity of `γ`

- `representablyFlat_of_comp_fullyFaithful`: if `F ⋙ i` is representably
  flat and `i` is fully faithful, then `F` is representably flat, since
  `StructuredArrow.post` is an equivalence of the categories of structured
  arrows.
- `representablyFlat_quasiEtaleSiteFunctor`,
  `representablyFlat_etaleSiteFunctor`: applied with
  `i = MorphismProperty.Over.forget _ ⊤ X`, the fully faithful inclusion of
  the quasi-étale (étale) category of `X` into `Over X`; the composite is
  `gSpaceOverFunctor hC X`.
- `gSpaceFunctor_map_apply`, `isOpenMap_gSpaceFunctor_map` and
  `image_mem_nhds_gSpaceFunctor_map`: for `f : T ⟶ S` in `P(G)` the point
  map of `X_T → X_S` is `Sigma.map f id`, an open map.
- `isContinuous_quasiEtaleSiteFunctor`, `isContinuous_etaleSiteFunctor`:
  by `Langlands.CategoryTheory.isContinuous_toGrothendieck` (module
  `FlatPrecoverageCoverPreserving`) it suffices that `γ` sends covering
  families of `DiscreteGSet.precoverage G` (jointly surjective families) to
  covering families of the equivariant (quasi-)étale precoverages. Every
  point `⟨s, y⟩` of `X_S` is `⟨f t, y⟩` for a member `f : T ⟶ S` of the
  family and `t ∈ T`. In the étale case this point is the image of `⟨t, y⟩`.
  In the quasi-étale case, the chart family of the presentation of `X_T` is
  a net (`isNet_chartFamily`); this gives finitely many charts whose union is
  a neighbourhood of `⟨t, y⟩`, and their images under the open map
  `X_T → X_S` form the required finite family with union a neighbourhood
  of `⟨s, y⟩`.
- `morphismOfSitesStatement`: the four results together.

## Provenance: internal

The statement is Berkovich's (see `SetInducedSiteStatement.md`); he gives no
proof. The route here is internal. Flatness is proved directly by the
cofiltered criterion, with the geometric input isolated in module
`CopiesOverHom`. Continuity follows from flatness and the preservation of
covering families, by the criterion of module
`FlatPrecoverageCoverPreserving`.
