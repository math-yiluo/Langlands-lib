# Differentiation of the real determinant

The determinant on the continuous endomorphisms of a finite-dimensional real normed space is smooth. The proof uses the determinant as a continuous multilinear map in the matrix rows in any fixed basis.

The differential at the identity is `continuousEndomorphismTrace`. Differentiating the row map replaces one identity row at a time and sums the resulting diagonal entries. At an invertible map `L`, multiplicativity of the determinant reduces the differential to the one at the identity. Applied to an increment `A`, the result is `det L * trace (L⁻¹ ∘ A)`.

This is an internal calculus lemma for the smooth Jacobian in real matrix conjugation coordinates.
