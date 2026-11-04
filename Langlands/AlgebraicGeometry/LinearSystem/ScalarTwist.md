# Scalar linear actions on the actual degree-one twist

This module reuses the published `Langlands.Scheme.Modules.unitAut` for
multiplication of an actual module sheaf by a global unit. Its existing
`unitAut_hom_app` computes the action on every open; the auxiliary
`unitAut_hom_app_top` specializes that formula to global sections.

`identityScalarPullbackIso` composes equality transport to the identity
pullback, the canonical identity-pullback isomorphism and the existing unit
action. Its coordinate formula is `pullback_identity_scalar_coordinate`.

`pullback_comparison_scalar` characterizes an isomorphism from the pullback
of a locally free rank-one module along `f = id` to itself when its action
on a family of sections whose frame opens cover is multiplication by `c`.
It is the canonical equality transport, followed by identity pullback and
the published `Langlands.Scheme.Modules.unitAut M c`, as packaged in
`identityScalarPullbackIso`. The proof uses the existing extensionality theorem
for the pulled-back covering sections and computes the canonical comparison
on those sections.

For any commutative coefficient ring `K`,
`linearChangeSections_smulOfUnit` computes the linear combinations for a
scalar matrix as multiplication by the scalar pulled back from `K`.
`relativeLinearActionTwistIso_smulOfUnit` then identifies the existing actual
relative linear-action comparison of the degree-one twist for a scalar
matrix with the canonical identity pullback comparison followed by
`Langlands.Scheme.Modules.unitAut`. Its unit is the image of `c` under `scalarsFromBase` for
the projective-space structure map composed with the coefficient-base map.
This retains the scalar on the line bundle under the known equality of the
scalar scheme action with the identity. The proof specializes the generic
comparison criterion to the covering homogeneous coordinate sections and
uses the existing coordinate formula for `relativeLinearActionTwistIso`.

These are derived consequences of the published module unit action, covering-section extensionality and relative
linear-action comparison. They prepare the degree-one comparison under
tensoring a frame module by a line bundle. The global tensor-line degree-one
comparison and ordinary moduli representability remain further obligations.
