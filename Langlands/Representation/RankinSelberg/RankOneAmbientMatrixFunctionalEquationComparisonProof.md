# Rank-one gamma comparison from ambient matrix data

Authors: Worker 458 (positive-rank proof and all-ranks assembly);
Worker 64 (rank-zero proof).

The theorem
`Langlands.RankinSelberg.rankOneAmbientMatrixFunctionalEquationComparison`
proves exactly the existing closed proposition
`RankOneAmbientMatrixFunctionalEquationComparisonStatement.{uF,uV,uW}`.
The proof introduces its full telescope and splits only on `n`. The field,
original carrier and ambient carrier universes remain independent. All
premises, the supplied additive measure, and the fixed polynomials, complex
unit and integer exponent are passed unchanged to the corresponding branch.
The existing statement and every previously published imported pair are
unchanged.

## Positive ranks

For `n = m + 1`, the proof applies
`AmbientMatrixComparison.gammaFactor` from the paired Positive module.
The actual inclusion embeds each bi-smooth coefficient of the original
coefficient model as the identical function in the ambient family. Only
ordinary and inverse-transpose common convergence bounds restrict to the
model. Actual coefficient-space transport supplies convergence of the
first-dual model and its complementary dual block.

One principal compact realization compares the original block and the
complementary dual block with the same averaged coefficient, Fourier test,
and nonzero extraction scalar `C`. It retains the supplied character's
conductor, the supplied self-dual measure, and the published signed-Weyl
conversion. For this coefficient the ambient data supply rational
continuations `RM`, `RMd` and their normalized equation. Multiplying both
continuations by the constant `C⁻¹` gives the literal block continuations.
`NormalizedFunctionalEquation.of_const_mul` cancels the common scalar in
the equation on the entire reduced-denominator domain. The published
`rankOneGammaFactor_of_normalized_blockZero_one` then supplies all
complementary blocks, nonzero model values, existence clauses, and
uniformity in compatible quotient measures and nonzero functionals.

## Rank zero

For `n = 0`, the proof applies
`rankOneAmbientMatrixFunctionalEquationComparison_zero` from the paired
ZeroPadic module. Its nonzero model integral comes independently from
`equalRankUnitValue` at the compatible `rankOneQuotientHaar`: an actual
compact model test has rational value one. This step uses full Whittaker
type and the nonzero functional, without an ambient generator witness.

For each actual pair of model vectors and row Schwartz test, the
one-by-one row homeomorphism transports the supplied-measure matrix
Fourier pair and both ambient continuations to the equal-rank integrals.
The actual model coefficient, with the constant second vector absorbed,
lies in the ambient family by the specified inclusion. The ambient
normalized equation therefore applies to that same coefficient.
`gamma_value_of_regular` gives the equation on the full regular domain,
and `equalRankGammaFactor_of_equation` supplies every compatible quotient
measure and nonzero functional pair. This branch works for every supplied
additive Haar measure and in particular for the self-dual measures
quantified by the closed proposition.

The two branches give the complete existing
`IsPadicSymmetricGammaFactor` for the original representation against the
trivial rank-one character, with exactly
`rationalGammaExpression (LocalFactor.residueReflection F) c a P PDual`.
Ambient normalized generators remain assertions on the ambient family.
No irreducibility, occurrence, representation equivalence, additional
analytic data, factor existence, or gamma-invariance premise is introduced.
The full Whittaker-type hypothesis retains reducible representations.

## Sources and provenance

This is an internal ambient extension of the existing matrix comparison,
rather than a literal numbered theorem from the literature. The paired
Positive and ZeroPadic modules document the implemented coefficient,
convergence, continuation, Fourier, compact-test, and measure arguments.
The final module assembles their proved conclusions by the exhaustive
natural-number cases.

Registered `jps-1979-gl3-i`, Jacquet--Piatetski-Shapiro--Shalika,
*Automorphic forms on GL(3) I* (1979), SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`:
printed p.177 fixes the matrix/Fourier convention; Proposition 3.1,
pp.185--187, supplies compact averaging; the function-space discussion on
p.183 and pp.188--190 supports the full Whittaker-type scope; Section 4.4
and Theorem 4.5 with its proof, pp.194--198, give the higher-rank
comparison context. These passages and their relevant displayed formulas
were read in the registered original during development.

Registered `jpss-1983-rankin-selberg`, the same authors,
*Rankin--Selberg Convolutions* (1983), SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`:
Section 5.4, pp.422--423, was read in the scanned original for the ambient
application motivation. The compact-test provenance of the rank-zero
helper also includes p.393. No unrestricted or finite-block
multiplicativity, Section 7 descent, or later analytic-base descendant
is used. The registered index and available project/Library errata notes
contained no source-specific correction affecting the cited passages.
