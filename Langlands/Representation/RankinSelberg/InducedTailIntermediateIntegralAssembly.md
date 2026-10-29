# Integral, continuation and span assembly for the intermediate tail

Supporting work by Worker 829 for the intermediate-rank calculation in JPSS
section 9.3, printed pages 456–457. These results are internal derivations from
Mathlib measure theory and the published Library zeta-value definitions. They
assume an explicit change-of-variables premise for the quotient measure and an
explicit pointwise comparison of integrands. They do not prove the quotient
disintegration, identify any actual integrand or construct any measure.

## Change of variables

Suppose a measure `μP` equals `ofReal C • map chart m` for a real `C > 0`. If
`chart` is a measurable embedding, then a complex function `f` is integrable
for `μP` exactly when `f ∘ chart` is integrable for `m`. In that case the
Bochner integral of `f` for `μP` is `C` times the integral of `f ∘ chart` for
`m`. The integral identity is a totalized identity and holds without an
integrability hypothesis. A second version replaces the measurable embedding
by an almost-everywhere measurable chart. It then needs `f` to be
almost-everywhere strongly measurable for the pushforward measure. Both
proofs substitute the measure identity and use Mathlib's
`integrable_smul_measure`, `integral_smul_measure` and the pushforward lemmas
(`MeasurableEmbedding.integrable_map_iff`, `MeasurableEmbedding.integral_map`,
`integrable_map_measure`, `integral_map`).

## Localized disintegration comparison

The core theorem `integrable_and_integral_of_localized_disintegration` uses
the product `m = (μQ.withDensity D).prod (η.prod ρ)` of a quotient measure
with density `D` and two parameter measures. The density `D` is measurable and
finite everywhere. The theorem takes as hypotheses:

- `Integrable f μP` is equivalent to `Integrable (f ∘ chart) m`;
- whenever `f` is integrable for `μP`, its integral equals `C` times the
  integral of `f ∘ chart` for `m`;
- for all `q, x, h`, the value `f (chart (q, (x, h)))` times the real density
  `(D q).toReal` equals `g q` times the indicator of `S` at `x` times the
  indicator of `U` at `h`, for measurable sets `S` and `U` of finite measure;
- `g` is integrable for `μQ`.

It concludes that `f` is integrable for `μP` and that the integral of `f` is
`C · η.real S · ρ.real U` times the integral of `g`. Taking the integral
consequence only for integrable `f` means the premises follow either from the
measure identity (via the change-of-variables theorems above) or from a
statement that provides only the integrability equivalence and the integral
formula for integrable functions.

The proof rewrites the left density onto the product measure with
`prod_withDensity_left`. A finite density turns integrability and the integral
for the density measure into those of the real-density multiple
(`integrable_withDensity_iff_integrable_smul'` and
`integral_withDensity_eq_integral_toReal_smul`). The pointwise hypothesis
turns this multiple into the localized product
`g q · 1_S x · 1_U h`. Worker 318's `integrable_localized_product` and
`integral_localized_product` (module
`InducedTailIntermediateComparison`) then give its integrability and evaluate
its integral as `η.real S · ρ.real U` times the integral of `g`.

Two small adapters cover the density `ofReal r ^ z` for `r > 0` and an integer
`z`. Its real value is `r ^ z`, and it is finite.

## Zero rectangular rows

The space of matrices with zero rows has exactly one point. Projecting away
this factor is therefore a measurable equivalence from `Q × Matrix (Fin 0) _ F`
to `Q`. The projection maps `μ.prod (dirac 0)` to `μ`, because the point mass
is a probability measure. So `UnequalRankConverges` with zero rows and the
unit point mass is equivalent to integrability of the quotient integrand at
the zero matrix (`unequalRankConverges_zero_rows_iff`). With the same
measures, `unequalRankIntegral` is the quotient integral of that integrand
(`unequalRankIntegral_zero_rows`, by `integral_dirac'`, since every function
on a one-point type is strongly measurable). The Library theorem
`rectangularMeasure_zero_rows` rewrites the rectangular measure with zero rows
to this point mass.

## Continuation and span

Assume actual Whittaker coefficients for `π` and `σ` converge on a right
half-plane. Assume also that there their integral equals `c` times a function
with rational continuation `R`. Then `RatFunc.C c * R` belongs to the
unequal-rank zeta values. The proof uses the Library's
`hasRationalContinuation_const_mul` and
`RationalContinuationLinear.continuation_of_eq_on_right`. If `c ≠ 0`, then
`R` itself lies in the Laurent span of these values: multiply by the Laurent
constant `C c⁻¹`, which the Library's `laurentToRatFunc_C` identifies with
`RatFunc.C c⁻¹`.

The combined theorem `mem_zetaSpan_of_localized_disintegration` works in the
zero-row full case with the unit point mass. It assumes the following for every
`s` in a right half-plane:

- the two change-of-variables consequences hold for the actual zero-row full
  integrand at the zero matrix;
- the pointwise localized comparison holds with a tail function `g s`;
- `g s` is integrable.

It also assumes that `s ↦ ∫ g s ∂μQ` has rational continuation `R`. It
concludes that `R` lies in the Laurent span of the actual zero-row full zeta
values. The scalar `C · η.real S · ρ.real U` is nonzero because `C`,
`η.real S` and `ρ.real U` are positive. Positive real volumes also imply that
`η S` and `ρ U` are finite. The scalar stays explicit in the integral identity
and is removed only at the span level.

## Provenance

Internal derivation; the measure-theoretic steps are standard Mathlib facts.
The motivating source is the registered `jpss-1983-rankin-selberg`, section
9.3, printed pages 456–457,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
This module does not formalize the source's computation as one step. The
measure-theoretic change of variables is an explicit premise. The pointwise
comparison is also a premise, to be supplied by the actual integrand
identification.
