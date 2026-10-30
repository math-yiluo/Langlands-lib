# Weighted block cones in diagonal coordinates

`Langlands.Exponents.diagonal_cone_of_weighted_block_cone` lifts a closed
positive-root cone for the size-weighted block vector `d_i * v_i` to the
actual diagonal vector `v (blockIndex E a)`. Its arguments and conclusion
are unchanged from the helper formerly private to
`TemperedOppositeTwistConeProof`. The proof and its two private supporting
lemmas were moved here for reuse by that module and
`SupportedRegularWeylParameterCones`; no new mathematical assertion is added.

The block-sum and block-prefix identities give zero total and nonnegative
partial sums at block boundaries. Within each block the vector is constant.
`MaximalConePolygon.pre_nonneg_of_antitone` interpolates between adjacent
boundary sums and supplies every interior cut. All ranks, including zero,
and every positive block size in the existing `BlockShape` are retained.

The interpolation argument was adapted by Worker 1008 from Worker 429's
published proof contribution. The supported-parameter comparison by
Workers 165 and 960 now uses this same declaration for its identical
weighted-block lifting clause.
