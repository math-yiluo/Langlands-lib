# Affine neutral models over a Dedekind base

This internal unit extends the published DVR model assembly to a Dedekind
base under explicit integrality and geometric connectedness hypotheses on
the generic group. It uses the represented relative identity component,
not a connectedness assertion about every fibre of the original model.

The published generic comparison identifies the generic fibre of the
relative identity-component inclusion with an isomorphism. The pullback
image formula therefore shows that its image contains the entire generic
fibre of the original model. The fraction-field spectrum maps to the zero
prime, by injectivity of the fraction-field algebra map.

The total model is integral by `IntegralModel.isIntegral_of_generic`.
The image of the relative identity-component inclusion is open and is
closed in every underlying fibre, by the published fibre comparison.
`AffineFiberwiseOpen.isAffineOpen_of_contains_generic_fiber` makes this
open affine. The open immersion identifies the representing group with
this affine open, proving that its structure morphism is affine.

`dedekindNeutralModel` retains this exact representing group, takes
flatness and finite type from its supplied smoothness, and composes the
published neutral generic comparison with the original generic
isomorphism. `dedekindNeutralInclusion` has the original inclusion as its
homomorphism and extends the identity on the given generic group.
The existence theorem uses published smooth relative identity-component
existence to choose a representative with smooth geometrically connected
fibres, then applies these constructions.

The construction retains smoothness of the original model and integrality
and geometric connectedness of its supplied generic group as hypotheses.
It does not prove reductivity or any comparison with Chevalley field
models; those are separate downstream obligations.
