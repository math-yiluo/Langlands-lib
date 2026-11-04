# Epsilon coefficients of dual-number matrices

`epsilonCoefficient` is the linear map that extracts the epsilon coefficient of
each entry of a matrix over `DualNumber A`. The coefficient ring and the matrix
index type have independent arbitrary universes. Extraction is a left inverse
of the existing `epsilonMatrix`.

Constant matrices on either side of an epsilon matrix multiply their
coefficients in the original order. In particular, extraction from
`inl(L) * epsilonMatrix(M) * inl(N)` gives `L * M * N`. No commutation of the
three matrices is asserted or used.

This is derived elementary algebra in Mathlib's actual trivial square-zero
extension. The proof expands matrix multiplication, uses the square-zero
extension multiplication formulas, and commutes its additive inclusion with
finite sums. The coefficient map is useful for successively differentiating
identities on all algebra-valued points, including identities for unipotent
group representations. This file makes no group-theoretic claim.

The two multiplication identities are reused from
`MatrixRepresentationDifferentialConjugation` under their published names
`constantMatrix_mul_epsilonMatrix` and `epsilonMatrix_mul_constantMatrix`.
The ordered sandwich identity applies these identities and then extracts the
epsilon coefficient.
