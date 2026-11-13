# Scalar ambiguity of conjugation on special linear groups

Author: Worker 239.

This is a derived internal matrix-algebra unit in the namespace
`Langlands.LinearAlgebra.SpecialLinearConjugation`. It works over an arbitrary
commutative ring `R` and any finite index type `I`, in independent universes.
There is no restriction on characteristic or matrix size.

`conjugation X` is the group homomorphism from `SL(I,R)` to `GL(I,R)`
that sends `g` to `X g X⁻¹`.

`mem_range_scalar_of_commute` proves that a matrix commuting with all of
`SL(I,R)` is scalar. The implemented proof applies Mathlib's elementary-matrix
criterion to each transvection viewed as a determinant-one matrix.
`exists_unit_scalar_of_commute` applies this to an invertible matrix, then
uses Mathlib's description of the center of `GL(I,R)` to obtain a unit scalar.
`exists_unit_scalar_of_conjugation_eq` gives the same conclusion when
conjugation fixes every element of `SL(I,R)`.

`exists_unit_scalar_of_conjugation_eq_conjugation` says that two invertible
matrices inducing the same conjugation on `SL(I,R)` differ by right
multiplication by a unit scalar. The proof conjugates their equality by the
inverse of the second matrix and applies the preceding criterion.
`eq_of_conjugation_eq_of_entry_eq_one` removes this ambiguity when a supplied
diagonal entry of both matrices is one: comparing that entry in the scalar
relation proves that the scalar is one.

These lemmas supply the scalar criterion and normalization step used in the
matrix descent of an outer type A group. They assert only the matrix facts
above; they do not construct a cocycle or a Hermitian presentation.
