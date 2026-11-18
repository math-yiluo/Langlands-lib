# Proof of local finite Cartan restrictions

`Langlands.LinearAlgebra.finiteCartanLocalStructure` proves exactly
`Langlands.LinearAlgebra.FiniteCartanLocalStructureStatement` at its two
independent universe parameters. The individual lemmas are in namespace
`Langlands.LinearAlgebra.FiniteCartanMatrix`.

Principal submatrices inherit the original positive integral symmetrizer.
For the vector obstruction, if every positive coordinate had a nonpositive
image coordinate, the symmetrized quadratic form would be nonpositive,
contradicting positive definiteness. Positivity of the determinant of each
rank-two principal submatrix gives `M i j * M j i < 4`; integer arithmetic,
off-diagonal nonpositivity and symmetric vanishing give the six possibilities.

For the row bound at index `i`, the proof uses the integer vector with
coordinate two at `i` and coordinate `-M j i` at every other index `j`.
It is nonnegative and nonzero. Its image under `M` is nonpositive away from
`i`, because the two terms involving the diagonal and column `i` cancel,
while every remaining summand is nonpositive. The image at `i` is
`4 - ∑ j ≠ i, M i j * M j i`. The positive-coordinate obstruction therefore
forces this integer to be positive, so the sum is at most three.

These are internal deductions from Mathlib's finite Cartan predicate. They
use neither a classification theorem nor group-theoretic hypotheses.
