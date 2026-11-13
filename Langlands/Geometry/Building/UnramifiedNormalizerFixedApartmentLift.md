# Rational normalizer translates lift to the fixed apartment

Author: Worker 229.

The Prop-valued `UnramifiedNormalizerFixedApartmentLiftStatement` states the
conditional lift assertion below for all the displayed field and group data.
The theorem `unramifiedNormalizerFixedApartmentLift_statement` proves it by
applying `unramifiedNormalizerFixedApartmentLift`.

This is an internal reduction toward Levi transport. The theorem
`unramifiedNormalizerFixedApartmentLift` assumes the published proposition
`UnramifiedTorusUnitFixedApartmentStatement`; it does not prove that proposition
or the full Levi transport target. With exactly the field, group, torus,
factorization, maximal splitness and full V6 assumptions of that target, it shows
that a rational normalizer translate of the image of a coefficient-fixed point
is the image of another coefficient-fixed point of the same apartment.

First, `IsFixedByScalarTorusUnits.normalizer_smul` applies the existing
unit-fixation conjugacy lemma to the inverse normalizer point and its induced
torus automorphism. This shows that the rational normalizer preserves fixation
by the scalar-extended torus units.

For the unramified theorem, a coefficient-fixed point makes its equipollence
class Galois-stable by `galoisStable_iff_equipollent`. The actual semilinear
coefficient action on the quotient fixes the normalizer translate because the
normalizer point descends from the base field. The preceding full V6 helper
`KPApartmentData.map_torusUnits_smul_apartmentMap` shows that the original point
is fixed by the units of `S_K`, using the scalar-extended factorization
`S_K → T_K → G_K`. The normalizer lemma transports this property to the
translated point. Applying `UnramifiedTorusUnitFixedApartmentStatement` to that
point gives the asserted coefficient-fixed lift.

The reduction supplies no Levi root-filtration conjugator; that geometric
prerequisite remains separate.
