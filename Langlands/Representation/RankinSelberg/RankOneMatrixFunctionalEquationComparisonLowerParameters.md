# Product parameters for the shifted lower affine slice

Author: Worker 623.

This internal coordinate helper parametrizes the already defined shifted
lower affine slice using the strict-upper scalar coordinates of the actual
upper-unipotent group and one scalar. The field is locally compact,
Hausdorff and second countable with Borel measurable space, and the supplied
additive Haar measure is sigma finite.

`shiftedLowerEntryEquiv n` identifies its free entries with an optional
strict-upper pair. The absent pair is the final first-column entry. A
strict-upper pair `(i,j)` corresponds to matrix position `(j,i+1)`.
`shiftedLowerParam n (X,a)` fills the final first-column entry with `a` and
these shifted positions with `-X_ij`. It fixes every other entry at the
negative superdiagonal, as in the actual shifted lower slice measure.

`shiftedLowerParam_preserving` proves that the actual product of
`upperEntryProductMeasure ν (n+1)` and `ν` pushes forward to
`shiftedLowerSliceMeasure ν n` exactly. The proof combines negation
invariance of additive Haar, finite product splitting, reindexing and the
preceding free-entry parametrization theorem. No normalization factor is
introduced. All sizes, including `n=0`, are covered.

`cyclicShiftMatrix n a` has negative superdiagonal and final first-column
entry `a`. `shiftedLowerParam_eq_transpose_mul` proves that, when `X` is the
actual strict-upper coordinate family of a group element `u`, the filled
matrix is exactly `transpose(u) * cyclicShiftMatrix n a`. The proof expands
the first column and each subsequent column, then uses the actual
unipotent diagonal and below-diagonal entry laws. Consequently
`shiftedLower_transpose_product_preserving` gives the same exact
measure-preserving parametrization written as this actual matrix product.
It uses the entry-product measure on coordinates of `u`; it does not
identify that measure with an arbitrarily normalized group Haar measure.

The provenance is internal finite-coordinate reindexing and composition of
published measure-preserving maps. No weighted Whittaker pushforward or
gamma functional equation is asserted.
