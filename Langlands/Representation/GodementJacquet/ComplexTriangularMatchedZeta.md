# Matched diagonal expansions of the complex matrix zeta integrals

`exists_complexMatrixZeta_matchedTriangular` rewrites a pair of
Godement–Jacquet integrals of a complex principal-series vector.
The primal test is a Schwartz function `Φ`. The dual test is its
entrywise trace Fourier transform, and the dual coefficient is the
original coefficient composed with inverse transpose. Each formula
holds on its own domain of absolute convergence.

The same Haar comparison constant works in both formulas. The primal
expansion integrates over the strict upper entries, leaving the
diagonal weights `χᵢ(zᵢ)|zᵢ|_ℂ^s` against a Schwartz marginal. For the
dual expansion the proof substitutes inverse transpose on the full
matrix group and then inverts the diagonal and unipotent coordinates.
This yields a lower triangular matrix test. The column Jacobian and
the inverted Borel weight leave the diagonal weights
`χᵢ(zᵢ⁻¹)|zᵢ|_ℂ^s`. Fourier covariance and complementary
inversion identify the dual marginal with the diagonal Fourier
transform of the same primal test.

These identities give the triangular zeta expansions for the matrix
integrals used by Jacquet, *Archimedean Rankin–Selberg Integrals* (2009),
§4.7 and §8. The diagonal meromorphic continuation and functional
equation are additional analytic steps.
