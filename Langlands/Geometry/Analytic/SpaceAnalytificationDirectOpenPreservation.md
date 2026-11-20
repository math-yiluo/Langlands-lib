# Open immersion preservation by affinoid tests

For separated algebraic spaces locally of finite type, a compatible
analytic morphism of an algebraic monomorphism is monic. Given two maps
with equal composites, the affinoid point comparison realizes the maps
on a common chart cover after a source isomorphism. Injectivity of the
comparison in the target and algebraic monicity identify the two
ring-valued points on every chart. Chart separation gives equality of the
original maps.

`compatibleAnalytificationIso` identifies a test-compatible map between
two supplied analytifications of one separated algebraic space locally of
finite type as the hom of an isomorphism. The preceding argument makes
the map monic. On a chart cover of its target, the affinoid comparison
represents each inclusion by a ring-valued point. Applying the other
analytification's affinoid comparison gives compatible local lifts.
Chart gluing gives a section, and monicity makes it an inverse.

For an algebraic open immersion, the affine étale tests of the source
compose to étale maps into the target analytification, so their jointly
surjective images make the image of the supplied analytic morphism open.
Its factor through this open domain is compatible with the original
test family by construction. The induced tests satisfy the
analytification axioms for the source. Naturality comes from the
original tests, étaleness follows by cancellation of the open inclusion,
and joint surjectivity follows from the definition of the image. A
pullback of affine tests over the source is also a pullback over the
algebraic target by monicity. The target analytification carries this
square to a pullback, and the square remains a pullback over the open
image because the open inclusion is monic. The factor through the open
domain is therefore an isomorphism by `compatibleAnalytificationIso`.

The constructions are internal consequences of the affinoid-point
comparison, chart gluing, and the Library's analytic domain and
analytification axioms.
