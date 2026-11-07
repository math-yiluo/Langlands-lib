# Finite coefficient and determinant identities

Author: Worker 1767.

This internal algebraic helper expands a finite product of linear power
series by subsets. Its coefficient of degree `n` is the sum of the products
indexed by the subsets of size `n`. With the multivariate polynomial variables
as coefficients, this is exactly the published `MvPolynomial.esymm`.

The determinant identity expands `det(A + t B)` by multilinearity in the rows.
The summand for a subset `s` is `t ^ card s` times the determinant whose rows
come from `B` on `s` and from `A` elsewhere. The implementation uses the
alternating multilinear map defining Mathlib's determinant and extracts each
row's scalar. These identities are valid over every commutative ring and do
not require distinct variables or a nonzero Vandermonde.

Taking coefficients in the power series version of this determinant identity
selects the subsets of exactly the prescribed size. When the second matrix
is obtained by multiplying column `j` of the first matrix by `x j`, the
resulting subset determinant sum equals the determinant of the first matrix
times the corresponding elementary subset sum. The proof factors the
power series matrix as the constant first matrix times a diagonal matrix
with entries `1 + x j * t`, then applies multiplicativity of the determinant
and the finite product coefficient formula.

The helper is derived from the finite product expansion and determinant
multilinearity. It does not itself prove a Whittaker formula or evaluate an
integral.
