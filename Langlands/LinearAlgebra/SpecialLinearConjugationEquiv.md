# Natural conjugation equivalences and inverse transpose

Author: Worker 239.

This internal algebra unit constructs conjugation by `X ∈ GL(I,R)` as an
automorphism of `SL(I,R)`, for any finite index type and commutative ring.
The determinant homomorphism shows that `X g X⁻¹` has determinant one.
Conjugation by `X⁻¹` is the inverse, and cancellation proves multiplicativity.
`toGL_conjugate` records the resulting formula in `GL`.

The inclusion of `SL` in `GL` and the conjugation construction commute with
every ring homomorphism. The proof applies the injective inclusion in `GL`
and uses multiplicativity of coefficient maps.

The unit also constructs the group homomorphism `inverseTransposeGL`,
`X ↦ (X⁻¹)ᵀ`. The inverse matrix is `Xᵀ`; reversing both multiplication
orders proves the group law, and transposing twice proves involutivity.
It commutes with coefficient maps and agrees with the existing
special-linear inverse transpose. Its group law gives
`θ(X g X⁻¹) = θ(X) θ(g) θ(X)⁻¹`.

These are direct consequences of the matrix and group operations already in
the Library and Mathlib. They provide algebra for changing local coordinates;
they impose no field or characteristic assumption and assert no descent or
existence of a special-linear presentation.
