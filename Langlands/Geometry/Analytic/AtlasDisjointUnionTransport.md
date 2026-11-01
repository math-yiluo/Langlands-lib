# Componentwise transport of disjoint unions of supplied affinoid atlases

Author: Worker 56. This internal construction uses the actual disjoint-union
presentation, complete bounded inclusions, and descent from
`AtlasDisjointUnionMaps`. It introduces no external source claim.

Let `I`, `J`, and `L` have a common index universe `z`. All component
presentations lie in `AffinoidAtlasPresentation.{u, max z v, max z w} K`
over a complete normed ultrametric field and have nonempty charts. Their
spaces may be empty, their index types may be empty, and their original
charts may overlap. The common category absorbs the component-index
universe into both its space and chart-index universes.

For any function `r : I → J` and complete arrows
`f i : A i ⟶ B (r i)`, `map` descends `f i` followed by the actual inclusion
of component `r i`. No injectivity or surjectivity of `r` is required.
The three projection lemmas identify the resulting map on points,
original chart indices, and actual bounded algebra pullbacks. It sends
`(i,x)` to `(r i, f i x)`, tags the original target chart with `r i`,
and retains the original bounded pullback of `f i`. The bounded identity
of the target inclusion disappears by algebra-map composition.

`inclusion_map` identifies the entire component restriction of the constructed
map. `map_id` proves its full identity law. `map_comp` proves that composing
two constructed maps composes both their reindexing functions and their
complete component arrows. These proofs use full-arrow extensionality from
the constructed coproduct: they retain the chart choices and dependent
bounded pullbacks, without recovering algebra maps from spectrum points.

Arbitrary original presentations can first be replaced by their same-space
nonempty subpresentations and their arrows by `Hom.nonemptyMap`. This does
not assert a chosen-category isomorphism to a presentation with deleted
empty charts. Arbitrary-source induction, analytic automorphism continuity,
refinement localization, and analytic sites remain separate.
