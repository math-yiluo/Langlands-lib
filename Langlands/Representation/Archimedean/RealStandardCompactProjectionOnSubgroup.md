# Compact projection on a subgroup containing the inducing rotations

`RealStandardCompactProjectionOnSubgroupStatement` considers a subgroup
of `O(n)` containing the diagonal signs and all rotations used in the
standard module's Fourier conditions. If a compact polynomial has the
required sign covariance and Fourier vanishing on that subgroup, the
Library's `compactProjection` agrees with the polynomial there.

The proof follows the two stages of `compactProjection`. At a subgroup
element, a sign average uses only its translate by another subgroup
element, and the required sign covariance fixes the value. A rotation
filter uses only the left rotation orbit in the same subgroup. Its
removed coefficients vanish, so it also fixes the value. Evaluation of
the final principal-series extension on `O(n)` restores this filtered
restriction.

The provenance is internal to the Library's `compactProjection`,
`signFilters`, and `highModesList`. The subgroup version will allow
prescribed products of block vectors to survive the global projection.
