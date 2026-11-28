# Finite-image scalar characters after a unitary twist

Let `D` be a finite-dimensional division algebra over a nonarchimedean local field `F`
with its module topology. Given a locally constant unitary character `ω` of `Fˣ`,
`exists_unitaryTwist_finite_range` gives a locally constant unitary character `χ`
of `Dˣ` such that `ω` times the scalar restriction of `χ` has finite image.

`divisionNormOrder` composes the determinant of left multiplication on `Dˣ`
with the additive order on `Fˣ`. The determinant is continuous by the matrix
determinant formula. Its restriction to scalars is the power of exponent
`Module.finrank F D`, so `divisionNormOrder_scalar` computes the order on
scalars by multiplying the field order by that exponent.
Choose a field unit `π` of additive order one, and a root `w` of `ω(π)⁻¹` of
that exponent. Its modulus is one. The twist at a division unit is the power of
`w` with exponent the additive order of its determinant. Local constancy of the
field order makes this twist locally constant. The scalar product character is
trivial at `π`, so each of its values is a value on the compact subgroup of
field units of order zero. A locally constant function on that compact subgroup
has finite image.
