# The real compact picture in opposite-cell coordinates

`Coordinates n` is the space of real vectors indexed by the strictly upper entry positions.
`oppositePoint z` is the transpose of the upper unitriangular matrix with entries `z`
(`oppositePoint_upperEntries`: it is `uᵀ` for the unipotent `u` with entry vector `z`); its
matrix depends affinely, hence smoothly, on `z` (`contDiff_oppositePoint_val`).

The Library's upper-Borel extension `PrincipalSeriesExtension.extension s φ` of a function `φ`
on `O(n)` factors on the opposite cell as

`extension s φ (oppositePoint z) = oppositeScalar s z · φ (oppositeCompact z)`
(`extension_oppositePoint`),

where `oppositeScalar s z` is the polarized Gram expression `gramExpression s 1` of the
complexified matrix and `oppositeCompact z` is its signed orthogonal Iwasawa part
`signedOrthogonalPart (oppositePoint z)`. The Gram expressions are smooth on invertible
matrices (`contDiffOn_gramExpression`), so the scalar factor is smooth
(`contDiff_oppositeScalar`); each entry of the compact factor is the real part of a Gram
expression with zero exponents, so the compact factor is smooth as a matrix-valued map
(`contDiff_oppositeCompact_val`). At the origin the factors are `1` and the identity matrix
(`oppositeScalar_zero`, `oppositeCompact_zero`).

`RealOppositeCompactChartStatement`: for every rank `n` and exponent vector `s` there are
`ρ > 0` and `C ≥ 0` such that for `‖z‖ < ρ`

`‖oppositeScalar s z - 1‖ ≤ C ‖z‖` and `‖oppositeCompact z - 1‖ ≤ C ‖z‖`.

`realOppositeCompactChart` proves it from the local Lipschitz property of `C¹` maps
(`ContDiffAt.exists_lipschitzOnWith`) on a common ball around the origin.

This is the real counterpart of the Library's `ComplexOppositeCompactChart`. These local
estimates are used in the approximation of real compact profiles near the identity in
`RealWhittakerApproximateIdentity`.
