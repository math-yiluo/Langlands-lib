# Actual rank-one block coordinates on the affine Fourier slice

This internal helper connects the complementary unipotent Fourier slice with
the actual block matrices used by the unequal-rank integrals.

`rankOneAffineParameters m` places a scalar `a` and an actual `m × 1` matrix
`X` in the row `(a, X_0, ..., X_(m-1))`. Its measurable equivalence has inverse
given by the first entry and the remaining entries as single-column rows.
`rankOneAffineParameters_preserving` proves that this map carries the product
of the supplied additive scalar Haar and `rectangularMeasure nu m 1` to
`rowMeasure nu (m+1)`. The proof uses the singleton product equivalence in
each row, followed by the finite product splitting at coordinate zero.
There is no volume or Jacobian factor, including when `m=0`.

`det_firstColumnMatrix` computes the determinant of the complementary slice
matrix as its first affine coordinate, for sizes `m+2`. This follows directly
from lower triangularity and the unit trailing diagonal.
`firstColumnMatrix_eq_blockMatrixAt` identifies that matrix with the actual
`unequalRankMatrix m 0 g X`, with only its natural-number rank transported by
`AdjacentBlockReduction.blockMatrixAt`, when the scalar is the unique entry
of `g` in `GL1`. Its proof compares every matrix entry, including the final
identity row. Thus the use of the rectangular block in this slice is an actual
matrix equality rather than a new name for the desired comparison.

The provenance is internal finite-coordinate algebra and product-measure
reindexing over the published definitions. This helper does not yet prove the
weighted Whittaker extraction or the gamma functional equation.
