# Gram congruence, quadratic isometry and tensor scalar extension

This internal comparison connects the matrix descent construction to Mathlib
quadratic forms. It works over a commutative ring with `2` invertible and an
arbitrary finite coordinate type.

For symmetric matrices `B₁` and `B₂`, `gramCongruent_iff_equivalent` identifies
`GramCongruent B₁ B₂` with equivalence of `B₁.toQuadraticForm'` and
`B₂.toQuadraticForm'`. These quadratic forms send a column vector `x` to
`xᵀ B x`. The Gram congruence convention is `Q B₂ Qᵀ = B₁`, so the
corresponding isometry sends `x` to `Qᵀ x`.

The definition `gramIsometry` constructs this actual linear isometry.
Conversely, the transpose of the matrix of any linear isometry supplies the
congruence. The proofs use the associated symmetric bilinear form and its
matrix, for which the matrix of a composition is `Mᵀ B M`.
Invertibility of `2` makes the passage from a symmetric matrix to its quadratic
form injective. Invertibility of the isometry matrix follows from bijectivity
of its linear map.

`gramBaseChangeIsometry B` compares the tensor scalar extension
`B.toQuadraticForm'.baseChange A` on `A ⊗[R] (n → R)` with
`(B.map (algebraMap R A)).toQuadraticForm'` on `n → A`.
Its underlying linear equivalence is `TensorProduct.piScalarRight`.
Equality of the quadratic forms is checked on the vectors `1 ⊗ x` using
`baseChange_ext`. This comparison needs no symmetry condition
on `B`.

The provenance is internal: the results follow from Mathlib's definitions of
matrix quadratic forms, associated bilinear forms and tensor scalar extension,
together with the explicit Gram congruence convention of
`OrthogonalCocycleComparison`. No Hasse principle is used.
