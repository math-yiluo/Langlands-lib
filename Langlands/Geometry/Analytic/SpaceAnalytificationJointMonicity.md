# Conditional joint monicity of analytified projections

This reduction assumes affine pullback preservation in the actual
spectrum-map form (`AffineTestPullbackPreservation`) and the published
localized functoriality proposition as explicit premises. Neither premise
is asserted as a theorem here.

`exists_algHom_of_affine_test_map` and
`algHom_comp_eq_of_affine_test_comp` use the fully faithful scheme Yoneda
embedding and the equivalence between relative spectrum maps and algebra
maps. They translate the maps between affine intersections to actual
algebra maps, including their composition equations.

`eq_of_affine_factorizations` considers two maps into the analytification
of an algebraic pullback, each factoring through an affine test. It forms
the intersections of the two tests over the two factors and their base.
Separatedness makes these intersections affine with finite polynomial
presentations. Equality of the two projected analytic maps lifts to each
factor intersection. Naturality and the base's affine-intersection
pullback property show that these lifts agree over the base intersection.
The assumed affine preservation gives a lift to their affine pullback.
The categorical intersection lemma identifies this as the intersection
over the original algebraic pullback. Naturality of the top point family
then equates the two full analytic morphisms.

`joint_monic_of_affine_and_etale_inputs` applies this affine
factorization lemma after a simultaneous étale source refinement through
charts of the top analytification. The actual analytic Hom-sheaf property
then descends equality to the original source. Localized étale pullback
existence and matching-point lifting are explicit hypotheses.

## Provenance: internal

This is a derived reduction of analytification's fibre-product property.
All analytic preservation and functoriality inputs remain explicit. The
conclusion concerns complete analytic morphisms, including their local
algebra maps, rather than just their maps of underlying points.
