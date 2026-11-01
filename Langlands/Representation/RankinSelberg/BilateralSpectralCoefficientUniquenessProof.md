# Uniqueness of absolutely convergent bilateral spectral coefficients

Authors: Worker 352 (Lean proof and verification) and Worker 486 (analytic
prerequisite specification and Fourier extraction rationale).

The theorem `Langlands.RankinSelberg.bilateralSpectralCoefficientUniqueness`
proves exactly the published closed proposition
`Langlands.RankinSelberg.BilateralSpectralCoefficientUniquenessStatement`.
This is a derived scalar analytic prerequisite for recovering formal bilateral
coefficients from equal absolutely convergent spectral sums.

## Scope

For every natural `q > 1`, the inputs are the original unrestricted functions
`a b : Langlands.HarmonicAnalysis.BilateralLaurentSeries`, indexed by all integers.
The hypothesis supplies one real `C`. At every complex `s` with `C < s.re`, the
norms of both actual weighted families are summable and their complex sums agree.
The weighting is precisely `spectralPoint q s ^ m`, where
`spectralPoint q s = (q : ℂ) ^ (-s)` and the subsequent exponent `m` is integer,
including negative integers. The conclusion is equality of the original functions.

The proof adds no support restriction, recurrence, finite comparison series or
analytic extraction premise. It recovers each coefficient separately by normalized
integration and cancels only a nonzero complex scalar.

## Implemented proof

Work on `AddCircle 1 = ℝ / ℤ` with Mathlib's `AddCircle.haarAddCircle`. This is
probability Haar measure, so integration over the circle has total mass one.
Write `e_m(x) = fourier m x`. For a real representative `t`, Mathlib's convention
is `e_m(t) = exp(2π i m t)`. Its Fourier coefficient at `n` integrates against
`e_(-n)`, fixing the sign and normalization used here.

First the private helper `fourierCoeff_tsum` proves, for any integer family `c`
with `Summable (fun m => ‖c m‖)`, that

```text
fourierCoeff (fun x => ∑' m : ℤ, c m * e_m(x)) n = c n.
```

Each character has norm one. Thus the original character series is absolutely
summable at every point, as established by `Summable.of_norm`. For the integrand
`F_m(x) = e_(-n)(x) * (c m * e_m(x))`, the proof shows the exact constant bound
`‖F_m(x)‖ = ‖c m‖`. Each `F_m` is continuous, hence strongly measurable, and
`Integrable.of_bound` gives integrability over the finite Haar measure. Because
the measure has total mass one, `∫ ‖F_m‖ = ‖c m‖`; these integrals are summable.

`integral_tsum_of_summable_integral_norm` now justifies the interchange of the
integer sum and the integral. The pointwise `HasSum` multiplied by `e_(-n)(x)`
identifies the integrated sum with the Fourier coefficient of the original sum.
Finally `fourierCoeff.const_mul` and `fourierCoeff_fourier` say that the integral
of the `m`th term is `c m` when `m = n` and zero otherwise. `tsum_eq_single`
therefore gives precisely `c n`. The extraction and all its convergence and
interchange hypotheses are proved within this helper.

The private helper `spectralPoint_vertical` proves the exact spectral identity

```text
spectralPoint q (σ - (2π t / log q) i)
  = spectralPoint q σ * e_1(t).
```

Here `σ` and `t` are real and the equality uses the project's actual complex
power. The assumption `q > 1` gives `log q > 0` and a nonzero complex base.
`Complex.cpow_def_of_ne_zero` expresses the power through the principal complex
logarithm; `Complex.natCast_log` identifies that logarithm with the real logarithm
of the positive natural base. Combining the two exponential factors and cancelling
the nonzero logarithm proves the formula. The helper `fourier_one_zpow` proves
`e_1(x)^m = e_m(x)` for every integer `m`, using `AddCircle.toCircle_zsmul` and
`Circle.coe_zpow`; this includes negative powers.

For the closing theorem choose `σ = C + 1` and set
`r = spectralPoint q (σ : ℂ)`. The published
`spectralPoint_ne_zero_of_pos` gives `r ≠ 0`. At the real parameter `σ`, the two
original hypotheses give summability of `‖a m * r^m‖` and `‖b m * r^m‖`.
For each real `t`, the parameter `σ - (2π t / log q) i` has real part `σ > C`.
The half-plane equality and the spectral identity therefore imply

```text
∑' m : ℤ, (a m * r^m) * e_m(t)
  = ∑' m : ℤ, (b m * r^m) * e_m(t).
```

Integer powers distribute over the complex product. Quotient induction on
`AddCircle 1` extends this equality from real representatives to every point of
the circle. Apply the proved extraction helper to both sides at an arbitrary
integer `n`; its norm summability hypotheses are exactly those obtained at `σ`.
This gives `a n * r^n = b n * r^n`. Since `zpow_ne_zero n hr` proves `r^n ≠ 0`,
`mul_right_cancel₀` yields `a n = b n`. Bilateral-series extensionality finishes.

## Provenance and boundaries

This unrestricted analytic uniqueness argument is internally derived; it is not
a literal theorem printed in JPSS. Its source conventions and intended use are
those of H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`. The retained PDF has SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp. 406–407 and 409–410 (one-based PDF pp. 41–42 and 44–45) were
visually read for this proof; no source-specific erratum was found in the
project's public notes.

JPSS (4.1), p. 406, supplies the unrestricted integer coefficient module and
explicitly permits torsion. Section (4.2), pp. 406–407, uses the spectral
substitution `X = q^(-s)` for determinant-slice sums; the particular source series
there have finitely many nonzero negative terms. Section (4.5), pp. 409–410,
motivates later coefficient identities after polynomial clearing and analytic
variation. The present proof uses absolute convergence on a vertical line and
works without either support bound. Its Fourier orthogonality and dominated
convergence dependencies come from the imported Mathlib modules
`Mathlib.Analysis.Fourier.AddCircle` and
`Mathlib.MeasureTheory.Integral.DominatedConvergence` in the prepared environment.

The result proves coefficient uniqueness alone. Laurent-action evaluation,
rational-denominator clearing, finite support, entire deformation and adjacent-rank
factor theorems remain separate assertions. No Laurent polynomial is cancelled
from the unrestricted bilateral module. The existing statement pair and all pairs
it imports remain unchanged.
