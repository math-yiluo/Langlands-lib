# Intersections of test objects over a pullback

`isPullback_intersection_of_isPullback` is a categorical lemma. Given
`W = X₁ ×[Z] X₂`, two objects mapping to `W`, their intersections over
`X₁`, `X₂`, and `Z`, and the natural maps between these intersections,
it identifies the intersection over `W` with the pullback of the first
two intersections over the third.

The proof shows the two projections from the proposed intersection agree
as maps into `W` by the joint monicity of its projections. It lifts a
compatible pair into the two lower intersections, equates their maps
into the base intersection, and applies the supplied pullback universal
property. Uniqueness follows by two applications of joint monicity.

## Provenance: internal

This is a derived categorical diagram lemma for the analytification
fibre-product proof. It uses only pullback universal properties and has
no geometric or analytic premises.
