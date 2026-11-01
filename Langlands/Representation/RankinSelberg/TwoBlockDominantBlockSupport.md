# Uniform rectangular support in a leading diagonal block

This is derived internal support infrastructure for the blockwise Iwasawa
approach to the dominant lower integral of JPSS (1983), Section 4.10(2),
printed page 419. It concerns an actual block sum whose leading block is an
unequal-rank matrix. It does not assert that the dominant matrix has already
been put in that form, and it asserts no integrability or volume estimate.

`blockSum_torus` identifies the actual block sum of two canonical torus
matrices with the torus of their concatenated exponent vectors.
`rootBounded_append_left` and `rootBounded_append_right` restrict adjacent
integer root bounds to the two consecutive blocks.
`blockSum_mem_integralOpen` checks entries of the matrix and its inverse.

`exists_coefficient_blockSum_rootBounded` decomposes both diagonal blocks
independently by the existing Iwasawa theorem. Their upper unipotent factors
form an ambient upper unipotent factor, their diagonal exponents concatenate,
and their integral factors combine with the supplied right integral factor.
The actual smooth coefficient's equivariance transports nonvanishing past
the upper unipotent factor. Its uniform smooth simple-root bound therefore
restricts to both chosen block decompositions. The root bound is chosen
before both matrices and the right integral factor.

`normalizedAbs_ratios_of_rootBounded` converts the integer adjacent
inequalities to bounds by the residue cardinality to that integer power.
`IsBlockSumRectangularSupport` defines the actual compact-support property
with this uniformity in all three supplied matrix coordinates.
`exists_blockSum_rectangular_support` applies the published
`unequalRankIwasawaSupport` to the leading block. The resulting compact set
is uniform in the leading group coordinate, every invertible matrix in the
other block, and every supplied right integral factor.

The only representation assumption is smoothness. The supplied functional
and coefficient may be zero, and all complementary rectangle dimensions
may be zero. The ambient block sum is required to have two positive ranks.
