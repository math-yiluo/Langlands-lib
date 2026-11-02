# Coherent degree-one twist comparisons on projective coordinate charts

For a scheme `S : Scheme.{u}`, any natural number `n`, a locally directed
open cover `𝒰` of `S`, and an actual `CoordinateCocycle n 𝒰`, this module
constructs `CoordinateCocycle.chartTwistIso`. For every index arrow `hij : i ⟶ j`
it is an isomorphism of module sheaves

`(d.chartFunctor.map hij)^* O(1)_j ≅ O(1)_i`,

where `O(1)_i` is the existing actual
`RelativeProjectiveSpace.twistOne (𝒰.X i) n`. The chart morphism is the
source chart's global-function linear action followed by the projective map
of `𝒰.trans hij`. No affineness restriction on the cover charts is imposed.

The isomorphism first applies inverse canonical pullback composition, then
the action pullback of the canonical relative twist base-change isomorphism,
then the actual linear-action twist comparison. `chartTwistData` packages
this particular isomorphism together with its coordinate law;
`chartTwistIso` selects that isomorphism.

For every coordinate index `l`, `chartTwistIso_coordinate` sends the pullback
of homogeneous coordinate `l` on chart `j` to
`changedRelativeProjectiveCoordinates (𝒰.X i).toSpecΓ (d.transition hij) l`.
This is the row-coordinate linear combination of the actual homogeneous
sections on chart `i`, with coefficients given by the actual transition
matrix over the global-function ring of `𝒰.X i`.

`chartTwistIso_id` proves that the comparison over an identity index arrow
is equality transport along the chart identity law followed by canonical
identity pullback. `chartTwistIso_comp` proves the full sheaf-morphism law:
pulling the comparison for `hjk` back along the chart map for `hij`, then
applying the comparison for `hij`, equals canonical pullback composition,
equality transport along the chart composition law, and the comparison for
`hij ≫ hjk`. These are equalities of actual module-sheaf morphisms.

The proof is internal derived infrastructure. The generic
`compositePullbackCoordinateIso` composes two actual coordinate-preserving
isomorphisms and proves its section formula using canonical pullback
composition and functoriality of section pullback.
`pullback_comparison_id_hom` and `pullback_comparison_comp_between` detect
identity and composition by equality on pulled-back sections whose frame
opens cover. The relative homogeneous coordinates supply precisely this
frame cover and the actual rank-one property.

For chart composition, `chartMap_toSpecΓ` proves compatibility of the chart
arrow with the global-function coefficient map. Naturality of scalar linear
combinations carries the second transition's coefficients through this map.
The coordinate cocycle composition law then identifies the resulting double
linear combination with the composite transition. The frame-cover criterion
proves equality of the sheaf maps. Thus every generic comparison hypothesis
is discharged by the constructed chart comparison and its coordinate formula.
No new external-source assertion is used.

This module supplies coherent twist comparisons on the existing chart
diagram. The line bundle on its glued scheme, a cubic embedding, and the
ordinary moduli representability conclusion remain separate obligations.
