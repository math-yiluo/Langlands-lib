# Chart binding of target-local finite models in the recognized source atlas

This internal module continues the target-locality development started in
`FullRecognitionFiniteTargetRefinement`. Take a family refinement `F` of a
recognized target affinoid `W`. The module binds the complete finite
algebra descent diagram `F.models.algebraDescentData` to actual saturated
charts of the recognized source atlas `A.atlas.fullRecognitionAtlas`.
Model algebras and the whole overlap maps are left unchanged.

The binding uses the full recognition atlas, not the original saturated
atlas. A source piece `V ∩ g⁻¹(chart)` need not lie in a single original
source chart, but it is always an actual local domain of one recognized
left preimage `F.left k`.

## A chart-change transfer lemma

`IndexedAffinoidAtlas.isMapChartChange_of_subatlas` concerns a locally
refining selection `P` of an atlas. Assume a chart-change law holds in the
subatlas and the source chart's image lies in the target chart. Then the
same law holds in the whole atlas. In the subatlas, both the given map and
the whole atlas's constructed chart change `changeMapChart` satisfy the
law, so uniqueness (`eq_changeMapChart`) identifies them. The constructed
chart change satisfies the law in the whole atlas.

## Pieces and canonical target domains

- `F.piece k` is the ambient trace of refinement chart `k`, and
  `piece_eq` shows it equals the range of the original target chart
  `index k`.
- `canonicalPullback_represents`: the canonical target map
  `F.models.rightCover.canonicalPullback k` represents the preimage of the
  piece in the spectrum of `target k`. Through the identity pair system
  (`fullRecognitionPairs_id`), the pair pullback of the recognized domain
  is a recognized restriction, which represents its locus. Composing with
  the inverse domain recognition equivalence keeps the representation.
- `targetDomain k` is the refinement chart as a domain of `target k` with
  this canonical map as structural map. `leftDomain k` is its pullback
  along the finite left base map. Its structural map is, definitionally,
  the local model's left map (`leftDomain_baseMap`).

## Model charts and their local domains

- `modelChart k` is the ambient chart of the `k`-th local model through
  `left k`. `range_modelChart` shows its range is exactly
  `V ∩ g⁻¹(piece k)`, using the chart compatibility of the actual pair
  pullback and the representation of `leftDomain k`.
- `modelSubdomain k D` makes a full domain `D` of the `k`-th model algebra
  an actual local domain of `fullRecognitionAtlas` on the chart `left k`,
  with the same algebra. `modelSubdomainMap` carries bounded restrictions
  along, and `modelSubdomain_locus` computes its locus as an image under
  `modelChart k`.
- `modelDomain k` is the whole model as a local domain. `modelIndex k` is
  the saturated chart with that locus, `range_modelIndex` computes its
  range, and `modelEquiv k` is the bounded comparison
  `localDomainSaturatedEquiv` with the saturated chart algebra.
- `overlapDomain i j` is the Library's whole model overlap domain
  `F.models.modelOverlapDomain i j`, made a local domain inside model `j`.
  `overlapDomain_locus` shows its locus is
  `range (modelChart i) ∩ range (modelChart j)`, by the models' ambient
  condition and injectivity of `W.chart`. `overlapIndex`, `overlap_range`
  and `overlapEquiv` give the matching saturated chart data.

## Overlap compatibilities and the binding

- `overlapToModelLeft_restriction`: the thin local-domain restriction from
  the overlap to model `i` is the first matching restriction
  `F.models.modelOverlapLeft i j` of the descent data. Domain restrictions
  are characterized by chart changes. The Library lemma
  `modelOverlapLeft_isMapChartChange_left` gives the chart-change law in
  the recognition source subatlas, and the transfer lemma above lifts it
  to `fullRecognitionAtlas`.
- `overlapEquiv_left` and `overlapEquiv_right` follow from naturality of
  `localDomainSaturatedEquiv`. They compare the saturated restrictions with
  the two matching maps of each overlap.
- `chartBinding` is a `ChartBinding` of
  `F.models.algebraDescentData.toPairTransitions` in
  `A.atlas.fullRecognitionAtlas.saturatedAtlas`, built with the Library
  constructor `ChartBinding.ofOverlapComparison` from the data above and
  the Library's `modelOverlapComparison`.
- `chartBinding_locus`: the gluing locus of the binding is
  `⋃ k, range (modelChart k)`.

## Provenance

This is internal infrastructure. It reuses the Library's finite-open
model overlap API (`modelOverlapDomain`, `modelOverlapLeft`,
`modelOverlapComparison`) and its chart-binding constructor. No
effective realization of the descent datum is assumed or constructed
here.
