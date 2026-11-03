# Contraction into a closed normal subgroup

This internal result works over any base scheme at arbitrary universe `u`.
Let `d : H → G` be a closed subgroup whose full range is normal on every
relative scheme, and let `χ : Gm → G` have full range contained in that of
`d`. Then `Dynamic.unipotent_le_range_of_normal` proves that every point
contracting to the identity under `χ` factors through `d`, on every relative
scheme test.

The proof uses the published extension definition of the dynamic unipotent
functor. For a contracting point `g` with orbit extension `e`, consider
`r(t) = e(t) g⁻¹`. On the multiplicative group this is the commutator
`χ(t) g χ(t)⁻¹ g⁻¹`. Since `χ(t)` lies in the normal subgroup, this
commutator lies in it. The published
`AffineLine.exists_lift_of_unitInclusion` extends this factorization across
zero through the closed immersion `d`. Evaluation at zero gives a lift of
`g⁻¹`, and inversion gives a lift of `g`.

For any supplied representative `iU : U → G` of `U_G(χ)`,
`normalUnipotentLift` constructs the actual homomorphism `U → H` using the
published represented-subgroup lifting interface. Its composition with `d`
is exactly `iU`, as proved by `normalUnipotentLift_comp`.

The argument is derived directly from the published definitions of range,
normality, orbit extension and represented-subgroup lifting, together with
the existing closed-immersion extension theorem. It requires no
smoothness, affineness, connectedness or field hypothesis. It does not
assert the existence or normality of an envelope, or smoothness or
surjectivity of a product map, or rational lifting for a quotient.
