# The field movement twist on original units

For an actual field embedding `ι : L →ₐ[K] D`,
`fieldMovementTwist ι a a' b` is the unit
`a * ι(a')⁻¹ * ι(b)` of the original division algebra.
The base, division algebra and embedded field may have independent
universes.

The theorem `move_unit_of_conjugate_fieldMovementTwist` assumes that
this twist is `u * ι(y) * u⁻¹` for actual units `u` and `y`. It produces
the single commutator `[u⁻¹, fieldMovementTwist ι a a' b]`. Multiplying
that commutator by `a` gives `ι(y * b⁻¹ * a')`, so the product is in
the actual field-unit image.

This is an internal group calculation. Its Lean proof uses the
definition of the twist, the unit homomorphism and the group identities;
membership in the actual commutator subgroup follows from the
commutator generator theorem. It does not establish the arithmetic
existence of the units or conjugacy.
