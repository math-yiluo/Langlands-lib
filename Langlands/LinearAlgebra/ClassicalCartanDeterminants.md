# Determinants of the classical Cartan matrices

For the integral Cartan matrices in Mathlib's numbering, the determinant
of type `A n` is `n + 1`, including rank zero. For types `B n` and `C n`
it is `2` in positive rank. For `D n` it is `4` in rank at least three.

Expand along the first row when the first vertex is linked only to
the second by entries `−1` in both directions. Expanding the off-diagonal
cofactor along its first column gives the recurrence `2 aₙ₋₁ − aₙ₋₂`.
Deleting the first vertex respects Mathlib's numbering for the types
`A`, `B` and `D` in the ranges needed by the recurrence. The low ranks
are computed from the displayed matrices, and the type `C` matrix is the
transpose of the type `B` matrix.

These internal computations complement Mathlib's exceptional determinant
formulas and supply the indices of the corresponding integral root lattices.
