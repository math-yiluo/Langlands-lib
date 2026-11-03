# Connected coordinate weight subgroups in the original group

This internal construction specializes the coordinate quotient and identity-component
interfaces to the original affine group and its actual split-torus automorphic action.
The field and common universe are arbitrary, and the additive character semigroup may
be empty or contain zero. The ambient group is smooth and affine.

The original coordinate algebra is smooth by the recovered group-scheme isomorphism
and the algebra-to-scheme smoothness comparison. The all-semigroup quotient theorem
makes `weightGroupScheme` smooth. Its actual identity component is
`connectedWeightGroupScheme`; composing its inclusion with `weightHom` gives
`connectedWeightHom` into the original group. The source is smooth, affine,
connected and geometrically connected, and the inclusion is closed and monomorphic.
Its range on all scheme tests is therefore a smooth connected closed subgroup.

The general identity-component tangent comparison gives equality of its tangent image
with the full coordinate subgroup's tangent image. The actual stability of that full
subgroup and the general identity-component action construction give stability on every
scheme test, an actual induced automorphic action, and equivariance of the inclusion.

For any connected source group, a homomorphism whose all-test range lies in the
coordinate subgroup factors through this connected subgroup. The factor first lifts
through the represented coordinate subgroup and then through its identity component.
The composite equation and uniqueness follow from the two factorizations and monicity.

These are internal specializations of `TorusActualWeightSubgroup`,
`TorusWeightRepresentative`, `CorepresentedSmooth`, `IdentityComponentAction`,
and the existing represented-subgroup factorization. No external assertion is used.
The exact action-weight tangent image, comparison with the generated semigroup functor,
source maximality and uniqueness, and split unipotence remain separate obligations.
