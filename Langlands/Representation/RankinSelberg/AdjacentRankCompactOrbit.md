# Compact support for adjacent-rank compact-orbit sections

This internal prerequisite formalizes the compactness argument preceding JPSS
Section 6.1, formula (11), on printed page 430 of the registered original
`jpss-1983-rankin-selberg`. It does not construct an induced section or assert a
Jacquet identity.

`AdjacentRankFullRank M` means that the rectangular matrix has a right inverse.
Right multiplication by an invertible matrix preserves this property.
For a rectangular matrix `[A,0]`, the property is equivalent to invertibility
of the square matrix `A`. The forward proof extracts the first rows of a right
inverse and takes determinants. The reverse proof extends the inverse of `A`
by a zero final row.

If a Schwartz function's topological support consists of full-rank matrices,
its restriction along `h ↦ [h,0]` has compact support on the actual group
`GL_n`. Indeed, intersect the compact support with the closed zero-last-column
slice, then project to the first columns. The resulting compact set consists
of invertible matrices, so the published GL embedding pulls it back to a
compact subset of GL. The restricted function vanishes outside that subset.
Rectangular right translation preserves the full-rank support condition and
gives the same compactness assertion for `h ↦ [h,0]g` for every ambient `g`.

The field is arbitrary and Hausdorff, with a topological division ring structure; the
matrix size includes zero. No norm or topology on a representation carrier,
Whittaker assumption, measure, or large-twist bound is used.
