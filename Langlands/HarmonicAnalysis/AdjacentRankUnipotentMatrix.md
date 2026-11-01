# Adjacent-rank unipotent matrices and phases

Worker 86, with the matrix and phase specification from Worker 1198. This is an
internal algebraic adapter for the existing adjacent-rank rectangular Fourier
target, derived from the published constructors and upper-unipotent matrix
properties. It requires only a field and includes rank zero.

For an actual upper-unipotent matrix `u` of size `r + 1` and a column `y`,
`adjacentRankLeftMatrix r u y` has first column `-y` and remaining columns
`-u i k.rev.succ`. Multiplication by the actual long Weyl matrix reverses
columns, and multiplication by the actual zeta diagonal negates all columns
except the last. The last column of the resulting rectangular matrix is the
first column of `u`, which equals the first basis column. Reversal of the
published epsilon column gives that same column. Entrywise calculation therefore
proves `adjacentRankLeftMatrix_join` with exactly the published right action.

The left antidiagonal sum splits into its last row, giving `-y (Fin.last r)`,
and its other rows, giving the negative sum of adjacent upper entries.
For the reversed unipotent matrix the shifted antidiagonal sum reindexes those
same adjacent entries by `Fin.revPerm`, giving `unipotentFourierSum r u`.
The two phase lemmas state these sums explicitly so that they can be used
without importing any other affine-slice development.

This module supplies algebraic matrix and phase identities. It asserts no
Fourier integral equality or identification of group and coordinate Haar measures.
