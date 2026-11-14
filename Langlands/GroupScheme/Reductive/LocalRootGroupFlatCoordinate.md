# Root-group coordinates over an arbitrary local ring

`LocalRootGroup.exists_coordinate_of_flat` extends the published
`LocalRootGroup.exists_coordinate` by removing its reducedness hypothesis.
The base is an arbitrary commutative local ring `R`. The group `G` is smooth
and affine, `i` is a map from a finite coordinate split torus, and `mu`, `nu`
are the chosen cocharacters. The field-fibre hypothesis is the same as in
`exists_coordinate`: on each field fibre the constructed dynamic subgroup
`U` is isomorphic to the additive group, with the torus acting through a
character whose pairing with `nu` is a fixed positive integer `m`.
The conclusion is a homogeneous element `x` of degree `m` for which
`R[X] → coordU`, given by evaluation at `x`, is bijective.

The implemented proof uses the published arbitrary-base smoothness of the
dynamic centralizer and its dynamic unipotent subgroup through
`LocalRootGroup.smooth_Uc`. This makes `coordU` a smooth, hence flat,
`R`-algebra. Its finite type property is already available. The closed
residue-field instance of the supplied fibre data gives a universal graded
line by `isUniversalLine_fibre` and `scaling_fibre`. The new
`GradedLine.exists_aeval_bijective_of_flat_of_universal` then supplies the
homogeneous polynomial coordinate without any reducedness assumption.
This is an internal consequence of those algebra and dynamic-subgroup
interfaces. It establishes polynomial coordinates only; a compatible
additive group law and the full root parametrization require further proof.

`polynomialCoordinateEquiv` chooses such a homogeneous coordinate and
packages its evaluation map as an `R`-algebra equivalence
`R[X] ≃ₐ[R] coordU`. This coordinate choice is not canonical.
