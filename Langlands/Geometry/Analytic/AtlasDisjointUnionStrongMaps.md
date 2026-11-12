# Disjoint unions in the category of compatible strong maps

Author: Worker 21.

The module `AtlasDisjointUnion` (Worker 56) constructs the disjoint union
`presentation A hA` of a family `A : I → AffinoidAtlasPresentation K` of
presentations whose charts all have nonempty spectrum (`hA`). Its space is the
topological sigma type `Σ i, (A i).space`, and its charts are the original
charts tagged by their component. `AtlasDisjointUnionMaps` (Worker 56) makes it
a coproduct in the category of chosen-chart maps. This module proves the same
universal property in the Library's category `CompatibleAtlasPresentation` of
compatible strong maps (all admissible chart pairs, with
`HasLocallyCompatiblePullbacks`). When the chart-index universe equals the
space universe, the Library's `saturationEquivalence` identifies that category
with the category of saturated presentations. The module
also shows that disjoint unions of quasi-isomorphisms are quasi-isomorphisms.

The universes follow `AtlasDisjointUnion`: `I : Type z` and
`A i : AffinoidAtlasPresentation.{u, max z v, max z w} K`, so the disjoint union
lies in the same category as its components. Namespace:
`Langlands.Analytic.AtlasDisjointUnion`. The compatible strong-map constructions
use `compatibleInclusion`, `compatibleDesc`, `compatibleDesc_pullback`,
`compatibleHom_ext` and `compatibleCofan` to distinguish them from the chosen-chart
constructions, so both morphism categories can be imported together.
`CompatibleStrongHom.pullback_congr` is in
`Langlands.Analytic.AffinoidAtlasPresentation`.

## Inclusions

- `image_sigmaMk_range`, `range_subset_of_image_subset`, `sigmaMk_injective`:
  the image of a chart of `A i` under `x ↦ ⟨i, x⟩` is the tagged chart.
- `CompatibleStrongHom.pullback_congr`: pullbacks of equal compatible strong
  maps agree.
- `inclusionStrong A hA i : StrongHom (A i) (presentation A hA)`: the base map
  is `x ↦ ⟨i, x⟩`. For a chart `c` of `A i` and a chart `d` of the union
  containing its image, the pullback is the union's restriction from `d` to
  the tagged chart `⟨i, c⟩`. The restriction law follows from transitivity of
  the union's restrictions.
- `compatibleInclusion A hA i`: the compatible version. Its pullbacks are pullbacks of
  the identity of the union, so compatibility is
  `StrongHom.hasCoherentPullbacks_id` of the union.
- `inclusion_pullback_self`: the pullback to the tagged chart itself is the
  identity.

## Descent

For compatible strong maps `f i : A i → B` into any presentation `B` in the
same universes:

- `descBaseMap f`: the continuous map `⟨i, x⟩ ↦ (f i).baseMap x`, continuous
  by `continuous_sigma`. `image_descBaseMap` computes images of charts.
- `descStrong f` and `compatibleDesc f`: the pullback at the tagged chart `c` is the
  pullback of `f c.1` at `c.2`. Containment of nonempty tagged charts forces
  equal tags (`tag_eq_of_subset`), so the restriction law reduces to that of
  one `f i`. Compatibility is inherited from the `f i`.
- `desc_baseMap_apply`, `compatibleDesc_pullback`: projection lemmas.
- `inclusion_comp_desc`: `(compatibleInclusion A hA i).comp (compatibleDesc f) = f i`. The proof
  compares one admissible pullback per chart (`ext_of_pullback`), computing
  the composite pullback through the tagged chart (`comp_pullback`).
- `compatibleHom_ext`: two compatible strong maps out of the union that agree after
  composing with every inclusion are equal. Base maps agree pointwise. For
  pullbacks, the composite with an inclusion computes the pullback at the
  tagged chart.

## Coproduct

- `compatibleCofan A hA`: the cofan in `CompatibleAtlasPresentation` with point
  `⟨presentation A hA⟩` and injections `compatibleInclusion A hA i`.
- `isColimitCofan A hA`: this cofan is a colimit (`Cofan.IsColimit.mk`, using
  `compatibleDesc`, `inclusion_comp_desc` and `compatibleHom_ext`).

## Disjoint unions of quasi-isomorphisms

For a second family `A'` with nonempty charts and compatible maps
`s i : A' i → A i`:

- `map hA hA' s := compatibleDesc (fun i => (s i).comp (compatibleInclusion A hA i))`, with
  `map_baseMap_apply` (`⟨i, x⟩ ↦ ⟨i, (s i).baseMap x⟩`) and
  `inclusion_comp_map`.
- `isQuasiIso_map`: if every `s i` is a quasi-isomorphism (`IsQuasiIso`:
  homeomorphism, and every admissible pullback represents the image of the
  chart), then so is `map hA hA' s`. The base map is `Sigma.map id`, a
  homeomorphism by Mathlib's `IsHomeomorph.sigmaMap`. For an admissible pair
  of tagged charts, a point of the nonempty source chart shows that the tags
  agree. The pullback is then that of `s i`, by `comp_pullback` through the
  untagged chart. Injectivity of `Sigma.mk` identifies the image loci.

## Provenance

This is an internal construction on the Library's disjoint-union atlas
(`AtlasDisjointUnion`, Worker 56) and compatible strong maps. It is the step
towards disjoint unions of analytic spaces needed for Berkovich's induced
spaces `X_{G/H}` (Berkovich, *Étale equivariant sheaves on p-adic analytic
spaces*, 1996 manuscript, registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.1.2, printed p.2: "X′ the disjoint union ∐_{i∈G/H} X_i"). No external
theorem is claimed beyond the Lean statements, all of which are proved.
