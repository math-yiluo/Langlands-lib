# Compact support in the complex Godement integral

`HasFullRowRank` expresses full row rank by a matrix right inverse. When the
rectangular test has compact support within this locus, the smaller group
variables that can meet the support lie in a common compact subset for the
larger group variable in any compact subset. The proof multiplies an admissible
rectangular matrix on the right by the inverse larger matrix. Its first
column is then zero and its trailing square submatrix recovers the smaller
matrix. The first-column condition cuts out a closed subset of the product of
the two compact sets. Full row rank forces the recovered square matrix to be
invertible there. This lets the proof take the compact image in the smaller
general linear group.

`ComplexGodementCompactStatement` gives absolute integrability of the
integrand and continuity of the resulting section for continuous inputs and
continuous compact tests supported in the full-row-rank locus.
`integrable_godementSectionIntegrand` combines the support bound with
continuity of the integrand and local finiteness of the measure. It gives
absolute convergence for every added complex character, as in Proposition
7.1(iii). For continuity in the larger group variable, the proof takes a
compact neighborhood of each point. The integral then agrees on that
neighborhood with the jointly continuous integrand integrated over the
common compact set in the smaller group. [Jacquet, *Archimedean Rankin–Selberg integrals*, §7.1, p. 43](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).

`HasFullRowRank` uses the right-inverse predicate `Langlands.RankinSelberg.AdjacentRankFullRank`.
