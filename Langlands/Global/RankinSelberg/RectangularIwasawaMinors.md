# Trailing minors in rectangular Iwasawa coordinates

This internal algebraic helper is derived from the published
`lowerBlockPair` coordinate formulas. It is intended for the local geometric
part of rectangular Mellin convergence; it does not assert an analytic
estimate or the final convergence proposition.

For an upper triangular matrix of rank `a+d`, its bottom `d` rows act on a
second matrix through its bottom square block. The implemented proof splits
the multiplication sum at `a` and uses triangularity to make the first sum
zero. Taking determinants and applying the triangular determinant formula
gives the product of the bottom diagonal entries times the corresponding
minor of the second factor. Column maps need not be injective.

For the actual matrix `lowerBlockPair g x 1`, the bottom principal minor is
one. Replacing its column `i` by leading column `j` gives the coordinate
`x i j` as its determinant. The proof identifies the submatrix with an
identity matrix with one updated column and applies Mathlib's
`Matrix.det_updateCol_sum`.

The definition `coordinateMinorColumns a d i j` names this replaced
column map: it is `Fin.natAdd a` except at `i`, where it takes the value
`j.castAdd d`.

These identities hold over any commutative ring, for arbitrary ranks,
including an empty trailing block. The coordinate identity has indices
`i : Fin d` and `j : Fin a`, so it makes no existence claim when either
index type is empty.
