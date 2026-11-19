# Smoothness of compactly supported real Godement integrals

`RealGodementSmoothStatement` proves smoothness in the translating
matrix of the real Godement inner integral with a smooth rectangular
test function and continuous lower-rank multiplier. The test support
is contained in a compact set of full-row-rank matrices. The
lower-rank Borel integration measure is finite on compact sets.

In the ambient matrix chart, the rectangular argument depends real
linearly on the translating matrix. Its continuous linear operator
depends continuously on the lower-rank integration matrix. Around a
fixed invertible translating matrix, choose a closed matrix ball
contained in the unit domain. The compact-support theorem puts all
lower-rank variables contributing in this ball in one compact set.

Restrict the integral to that compact set and apply the Library's
smoothness theorem for compact integration of a linear-parameter
family. On the smaller open ball the restriction leaves the integral
unchanged, so the original integral is smooth there. This works at
every invertible matrix and gives manifold smoothness via the
open unit chart.

This is the smoothness part of the compact-support construction
underlying Jacquet's Godement section (7.1), with the bottom rows
for the Library's upper triangular Borel. Principal-series
equivariance and generation of sections are separate properties.
[Jacquet, *Archimedean Rankin–Selberg Integrals*, §7.1, pp. 43–46](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
