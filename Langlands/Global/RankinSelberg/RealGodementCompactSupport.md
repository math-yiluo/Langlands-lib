# Compact full-row-rank support in the real Godement integral

`RealGodementCompactSupportStatement` proves absolute convergence for
every complex exponent and holomorphy of the inner integral with a
continuous test function supported on a compact subset of full-row-rank
rectangular matrices. Its other factors are a continuous complex
multiplier and the exponential of the complex parameter times a
continuous real weight. The integration measure on the lower-rank
group is Borel and finite on compact sets.

The rectangular argument is the last `m` rows of the translating
matrix left-multiplied by the integration matrix `h`. This is
`(0,h) g`, the row placement for the upper triangular Borel. The
inverse recovery map multiplies the rectangular argument by `g⁻¹`
and drops its first column. On its image this recovers `h`.
A right inverse for the rectangular matrix yields a right inverse
for `h`, so full row rank forces the recovered matrix to belong to
the lower-rank general linear group.

Over a compact set of `g`, the pairs of translating matrices and
rectangular arguments that are recovered this way form a closed
subset of a compact product. The recovery map sends them to a
compact subset of the ambient square matrices consisting of units.
The embedding of the unit group transfers that compactness to the
integration domain. In particular all real exponential moments of
the continuous integrand are integrable. The Library's holomorphy
theorem for integrals with exponential moments gives the conclusion.

This gives the compact-support convergence of the inner integral
in Jacquet's equation (7.1) and Proposition 7.1(iii), using the
upper triangular Borel placement and a general continuous real
weight in place of the logarithm of the absolute determinant.
The smooth section law and generation of the principal series
require further results from §7.1.
[Jacquet, *Archimedean Rankin–Selberg Integrals*, §7.1, pp. 43–46](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)

`HasFullRowRank` uses the right-inverse predicate `Langlands.RankinSelberg.AdjacentRankFullRank`.
