# Proof of norm-convergent monomial expansion

Authors: Worker 36 (original construction), Worker 56 (coefficient generalization).

`Langlands.Analytic.StrictTateAlgebra.monomialExpansion` proves the exact
`MonomialExpansionStatement` for independent variable and coefficient-ring
universes. The monomial and coefficient-map constructions, including their
intrinsic norm bounds, are in `TateSeries.Definitions`.

The coefficient monomials of a restricted series tend to zero along the
cofinite filter in the Gauss norm, because their norms are the coefficient
norms. In the complete nonarchimedean additive group of Tate series this
implies unconditional summability. Each continuous coefficient map commutes
with this sum and leaves exactly one nonzero summand. Formal-series
extensionality therefore identifies the sum with the original series.
The resulting summability and sum identity give `HasSum` and the closing
theorem.

Completeness is required only for summability and the expansion identity.
The proof works over an ultrametric normed commutative coefficient ring and
does not divide coefficients. It assumes no division, preparation or
normalization theorem. Original-source scope is recorded in the paired
`TateSeries/Statement.md`.
