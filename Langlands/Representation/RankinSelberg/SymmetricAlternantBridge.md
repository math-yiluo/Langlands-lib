# Complete symmetric convolution and alternant bridge

Author: Worker 1767.

This internal algebraic development derives a finite convolution for the complete
symmetric polynomials from their published generating series. Removing one
linear factor from the elementary product leaves, after multiplication by the
complete generating series, the geometric series in the corresponding variable.
The removed-factor product has degree less than the number of variables.
Negative complete symmetric degrees are interpreted as zero, exactly as in
`completeSymm`. No analytic convergence is asserted.

The convolution is reindexed in reverse degree order to construct a single
coefficient matrix, independent of the weight. For every coordinatewise
nonnegative integral weight, multiplying the Jacobi–Trudi matrix by this
coefficient matrix gives the monomial matrix with entry
`X k ^ (α i - i + n).toNat` in rank `n + 1`. Nonnegativity ensures that the
exponent before conversion to a natural number is nonnegative.

At weight zero the Jacobi–Trudi determinant is one, so the determinant of
the coefficient matrix equals the base monomial determinant. This base matrix
is the row reversal of the transpose of the Vandermonde matrix. Its determinant
is nonzero when the coefficient ring is a domain, since the multivariate
polynomial variables are distinct. For every commutative coefficient ring the
matrix multiplication also gives the cross-multiplied bialternant identity:
the Jacobi–Trudi polynomial times the base alternant equals the weight
alternant. This polynomial identity remains valid after any specialization,
including repeated parameter values; it contains no division by a specialized
Vandermonde.

All results are internal consequences of the complete generating series,
finite coefficient convolution, determinant multiplicativity, the zero-weight
Jacobi–Trudi identity, and Mathlib's Vandermonde determinant criterion.
They do not identify any Whittaker model or evaluate a Rankin–Selberg integral.
