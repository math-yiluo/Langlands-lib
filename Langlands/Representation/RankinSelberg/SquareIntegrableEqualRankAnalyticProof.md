# Square-integrable equal-rank convergence and holomorphy

Author: Worker 462. Worker 161 contributed the square-domination route used in
the convergence argument.

This module proves the unchanged Library proposition
`Langlands.RankinSelberg.SquareIntegrableEqualRankAnalyticStatement.{uF,uV,uW}`:

```lean
theorem squareIntegrableEqualRankAnalytic :
    SquareIntegrableEqualRankAnalyticStatement.{uF, uV, uW}
```

For every prime, `PadicField` with supplied topological data `T`, and positive
rank `n + 1`, it keeps the nontrivial unitary additive character, the
right-invariance instance for `unipotentHaar`, and every compatible quotient
measure. The two representation-carrier universes remain independent. For two
irreducible representations satisfying the analytic `T.IsSquareIntegrable`
hypotheses, every standard and inverse functional, their actual coefficient-model
vectors, and every Schwartz–Bruhat test, it proves `EqualRankConverges` for every
`s` with `0 < s.re` and complex `DifferentiableOn` of the actual
`equalRankModelIntegral` on that half-plane. Rank one and zero functionals,
vectors and tests are included. No hypotheses are added to the proposition.

## Convergence

All helpers in this module are private derived adapters for the existing
quotient definitions. The final theorem uses the published
`Langlands.RankinSelberg.weightedWhittakerSquare` from
`Langlands.Representation.RankinSelberg.WeightedWhittakerSquareProof`, once at
`{uF,uV}` for the first representation and once at `{uF,uW}` for the second.
That theorem derives both character signs of the square estimate from the
analytic matrix-coefficient square-integrability hypotheses; this module does
not assume a Whittaker square estimate or convergence as an additional premise.

The helper `sqrtNormTest Φ` has value `(Real.sqrt ‖Φ x‖ : ℂ)`. Composition
preserves local constancy, and its support is contained in that of `Φ`, so this
is a Schwartz–Bruhat test. Its squared norm is exactly `‖Φ x‖`. Applying the
standard-character square estimate to the first representation and the
inverse-character estimate to the second, with this test and
`a = s.re / 2 > 0`, gives integrability of

\[
 A(q)=|W(q)|^2\,|\Phi(e_{n+1}q)|\,d(q)^{\operatorname{Re}s},\qquad
 B(q)=|W'(q)|^2\,|\Phi(e_{n+1}q)|\,d(q)^{\operatorname{Re}s},
\]

where `d = quotientDeterminantAbs (normalizedAbsoluteValue T) n` and the two
Whittaker absolute values are the published `whittakerNorm` and
`inverseWhittakerNorm`. These are actual functions on the left-unipotent
quotient. The norm formula for the actual equal-rank integrand follows on
quotient representatives from multiplicativity of complex norm and the norm
formula for a positive real base raised to a complex power. The nonnegative
square `(|W(q)| - |W'(q)|)^2`, multiplied by the common nonnegative weight,
bounds that norm by `(A(q) + B(q)) / 2`.

Measurability follows for the supplied topology: `T.IsSquareIntegrable` implies
admissibility and hence smoothness, so the published
`equalRankIntegrandContinuous` gives continuity of the actual integrand for
every complex parameter. The quotient has its target Borel structure, hence
the integrand is almost-everywhere strongly measurable for every quotient
measure. `Integrable.mono'` with the preceding bound proves the required
Bochner integrability. The same argument includes zero data without case splits.

## Holomorphy

On quotient representatives the actual integrand factors as

\[
 I_s(q)=I_0(q)\,(d(q):\mathbb C)^s.
\]

The published determinant-norm positivity theorem gives `d(q) > 0`.
Continuity of the normalized absolute value supplied by `T`, continuity of the
determinant on the general linear group, and quotient descent prove continuity
and hence measurability of `d`. The preceding measurability argument applies to
`I_0` as well.

The module applies the published `Langlands.Analysis.mellinHalfPlane` from
`Langlands.Analysis.MellinHalfPlaneProof`, with coefficient `I_0`, weight `d`
and shift zero. Its real-axis integrability hypotheses are supplied by the
already proved convergence at `(t : ℂ)` for every `t > 0`. The factorization
identifies its Bochner integral with `equalRankIntegral`; unfolding
`equalRankModelIntegral` gives the required function. This proves exactly
`DifferentiableOn ℂ` on `{s : ℂ | 0 < s.re}`. No sigma-finiteness or extra
integrability assumption is introduced.

The private assembly takes two universe instances of the weighted-square
proposition as internal arguments. The final closed theorem supplies both with
the published proof. All conclusions therefore follow from the unchanged
target hypotheses. The proof uses only `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics **105** (1983),
Section 8.3, printed pp. 448–451; registered source
`jpss-1983-rankin-selberg`, retained PDF SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original pages are zero-based PDF indices 82–85. No source-specific erratum
was found in the project, Library or literature errata locations.

The proposition on p. 448 asserts absolute convergence and convergence locally
uniform in the half-plane. The square estimates and integration formulas on
pp. 449–450 underlie the imported weighted-square proof; p. 451 also displays
the weighted-square Cauchy–Schwarz factor. This module implements the elementary
square-domination consequence of those estimates, followed by the general
Mellin holomorphy theorem. Page 451 leaves normal convergence to the reader.
The complex differentiability conclusion here is the derived formulation in
the target Markdown, discharged by that Mellin theorem. This module makes no
local-factor, rationality or normalized-generator assertion.
