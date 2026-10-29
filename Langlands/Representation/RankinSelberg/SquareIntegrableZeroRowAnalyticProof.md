# Sharp zero-row convergence and holomorphy

Author: Worker 161.

`Langlands.RankinSelberg.squareIntegrableZeroRowAnalytic` proves exactly
`SquareIntegrableZeroRowAnalyticStatement.{uF,uV,uW}`. For the supplied
irreducible analytically square-integrable representations, the actual
zero-row unequal-rank integral converges absolutely and is
`DifferentiableOn ℂ` on `{s : ℂ | 0 < s.re}`.

The proof retains every prime, supplied topological structure, compatible
left-unipotent quotient measure, additive Haar measure, rank expression,
functional and coefficient-model vector in the target. The field and two
representation carriers have independent universes. Zero functionals and
zero vectors are included. There is no additional convergence, holomorphy
or nonvanishing hypothesis, and no assertion at the boundary or for other
rectangular blocks.

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics **105** (1983),
Section 8.3, printed pp.448–451, especially restriction estimate (7) on
p.450 and the Cauchy–Schwarz argument on p.451. The registered source is
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The pages were read visually at one-based PDF pp.83–86, zero-based
indices 82–85. No registered errata note was found.

## Reduction to the quotient integral

The zero-row rectangular matrix space is a singleton. The explicit
measurable equivalence `zeroRowProductEquiv` from its product with the
left-unipotent quotient to that quotient is the first projection.
`rectangularMeasure_zero_rows` identifies the rectangular measure with
the Dirac probability measure. Measure preservation of the first
projection transfers integrability in both directions, without a
sigma-finiteness assumption on the quotient measure. This proves
`zeroRow_converges_iff` for the actual `UnequalRankConverges`.
Dirac integration also reduces the existing nested integral to the
quotient integral in `zeroRow_integral`.

The auxiliary zero lemmas show that either zero Whittaker function
gives the zero integrand, convergence at every complex parameter and
an entire integral. Surjectivity of `modelMap` shows that a zero
functional gives a zero coefficient function. The final assembly
handles these cases directly through estimates valid for all data;
it needs no case split or nonzero-functional assumption.

Continuity of the quotient integrand is supplied by the published
`Langlands.RankinSelberg.unequalRankZeroRowIntegrandContinuous` from
[`UnequalRankZeroRowIntegrandContinuityProof`](UnequalRankZeroRowIntegrandContinuityProof.md).
That result uses local constancy of smooth matrix coefficients, continuity
of the rank inclusion and determinant weight, and the open quotient-map
criterion. Its continuity conclusion gives almost-everywhere strong
measurability for every quotient measure.

## The two square estimates

Put `r = k + 1`, `d(q) = quotientDeterminantAbs abv n q`, and let
`c(q)` be the actual quotient integrand at real parameter `r/2`.
At this parameter its determinant weight is one. Quotient induction
proves the exact identity

\[
 I_s(q)=c(q)\,(d(q):\mathbb C)^{s-r/2}.
\]

The published `zeroRowLastRowCutoff` gives a Schwartz–Bruhat function
`Φ` whose multiplication preserves the original restricted larger-rank
coefficient. Taking norms of this preservation equality yields

\[
 \lVert c(q)\rVert=u(q)v(q),\qquad
 u(q)=\lvert W(\operatorname{diag}(g,I_r))\rvert,\quad
 v(q)=\lvert W'(g)\rvert\,\lvert\Phi(\operatorname{lastRow}(g))\rvert .
\]

Only preservation is used; the stronger zero-or-one property of the
published cutoff is unnecessary here. No coefficient is replaced by
a smeared coefficient.

The published `squareIntegrableWhittakerRestriction` supplies
integrability of `u² d^(-r)`. The inverse-character conjunct of the
published `weightedWhittakerSquare` supplies integrability of
`v² d^(2a)` for every real `a > 0`. These are precisely the two
square factors in the source's p.451 argument.

The elementary lemma `integrable_of_two_square_bounds` proves integrable
domination using `a*b ≤ (a²+b²)/2`. Applying it to
`u d^(-r/2)` and `v d^(s.re)` proves integrability of `I_s` for every
`s.re > 0`: their squared factors are exactly the two supplied estimates.
This gives the needed finiteness consequence of Cauchy–Schwarz; no
optimal numerical integral bound is asserted. The singleton-product
adapter then gives the target's joint Bochner integrability.

## Holomorphy and supplied data

The quotient determinant absolute value is continuous and positive.
The coefficient `c` is almost-everywhere strongly measurable, and the
preceding argument gives Mellin integrability at every positive real
parameter. The published theorem `Langlands.Analysis.mellinHalfPlane`
therefore proves differentiability of the quotient Mellin integral
throughout the half-plane. The exact factorization and
`zeroRow_integral` identify this function with the actual
`unequalRankModelIntegral`.

The source leaves normal convergence to the reader. The imported
Mellin proof supplies the derived analytic step: around each parameter
it chooses two positive real endpoints, bounds powers by their endpoint
values, and bounds the logarithmic derivative by a constant times the
sum of the two endpoint norms. Those endpoint functions are integrable
by the square-estimate argument. Dominated differentiation of the
actual integral gives `DifferentiableOn`, without finite or
sigma-finite measure assumptions.

`squareIntegrableZeroRowAnalytic_of_estimates` installs the exact target's
supplied topology, valuation, local-field and Borel structures.
`IsSquareIntegrable.isAdmissible` supplies smoothness for each
representation. Continuity of the normalized absolute value follows
from `NNReal.continuous_coe.comp T.continuous_normalizedAbsHom`.
The compatible measure is passed unchanged to both estimates, and the
arbitrary additive Haar measure is retained in the zero-row reduction.

`squareIntegrableZeroRowAnalytic_of_weighted_square` supplies the first
estimate with `squareIntegrableWhittakerRestriction`. The final theorem
supplies the remaining estimate with `weightedWhittakerSquare`.
Both estimates, the cutoff and the Mellin theorem are imported from
published proof modules by Lean name. Their implementations and the
target's Lean/Markdown pair are unchanged. All local adapters above are
derived from the existing definitions and Mathlib; they introduce no
new representation-theoretic assumption.
