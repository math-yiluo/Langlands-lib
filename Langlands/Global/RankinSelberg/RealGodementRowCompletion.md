# Smooth completion of real full-row-rank rectangles

`RealGodementRowCompletionStatement` constructs a smooth square
matrix from an `m` by `m+1` real rectangle. The last `m` rows are
the given rectangle. On the full-row-rank domain the square matrix
has positive determinant.

The new first row consists of signed maximal minors. Expansion of the
determinant along that row gives a sum of squares of maximal minors.
A right inverse for the rectangle makes the determinant of their
product one. Cauchy–Binet then gives a nonzero maximal minor, since
every `m`-element subset of the columns is the complement of a
singleton. This proves positivity. Conversely, the last columns of
the inverse of a completed square matrix supply a right inverse for
the rectangle. Full row rank is therefore the preimage of the open
unit domain under the smooth completion.

Each added entry is a signed determinant of a linear submatrix, hence
smooth. The completed units provide a choice of translating matrix
over the rectangular domain. This is a Library-specific ingredient
for the descent of smooth principal-series test data to rectangular
matrices in the compact-support Godement construction.
[Jacquet, *Archimedean Rankin–Selberg Integrals*, §7.1, p. 46](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
