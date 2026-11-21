# Determination by Gaussian-weighted directional moments

Let `(H, ν)` be a measure space, `E` a finite-dimensional real normed space
with its Borel measurable structure, `p : H → E` a measurable map, and
`F : H → ℂ` a measurable weight. The spaces can have independent universes.
`GaussianWeightedMomentDeterminationStatement` assumes that
`exp(-‖p(h)‖²/2) F(h)` is integrable and that for every continuous real
linear form `L : E → ℝ` and every `n : ℕ`,

\[
\int_H L(p(h))^n\,\exp(-\|p(h)\|^2) F(h)\,d\nu(h)=0.
\]

It concludes that `∫ h, g (p h) * F h ∂ν = 0` for every measurable
`g : E → ℂ` for which `g(p(h)) F(h)` is integrable. In particular the
conclusion uses the original weight, without the Gaussian. There is no
finiteness assumption on `ν`, global integrability assumption on `F`, or
injectivity assumption on `p`. The proof is `gaussianWeightedMomentDetermination`,
with the pointwise API `integral_eq_zero_of_gaussian_moments`.

The same half-strength bound implies integrability of each full-Gaussian
moment (`integrable_gaussian_moment`) and of the undamped product for bounded
measurable `g` of compact support (`integrable_mul_of_hasCompactSupport`).
The first auxiliary result does not need finite dimensionality, and the
second only uses the norm topology and measurable structures needed for its
integrability hypothesis and conclusion.

## Lean proof

Put `w = exp(-‖p‖²) F`. The operator norm estimate and
`(‖L‖ - ‖p(h)‖)² ≥ 0` bound `exp(|L(p(h))|) |w(h)|` by
`exp(‖L‖²/2) |exp(-‖p(h)‖²/2) F(h)|`. This gives integrability of the
exponential majorant and of every moment, using
`|L(p(h))|^n ≤ n! exp(|L(p(h))|)` for the latter.

Each of the real and imaginary parts of `w` inherits the zero moments since
its projection is continuous real-linear and commutes with the integral.
For either real component `v`, the sum of the norms of the terms of
`exp(i L(p(h))) v(h)` is `exp(|L(p(h))|) |v(h)|`, bounded by the same
integrable majorant. The exponential series and integrated dominated
convergence therefore give zero integral against `exp(i L(p(h)))` for each
`L`.

The positive and negative parts of `v` define finite positive measures with
respect to `ν`. Their pushforwards along `p` have the same characteristic
functions on the real continuous dual by the preceding zero integrals.
Finite-dimensionality supplies completeness and second countability for
Mathlib's `Measure.ext_of_charFunDual`, which identifies the pushforwards.
Subtracting the two transported integrals shows that each component, hence
`w`, has zero integral against every integrable measurable pullback test.
Applying this to `x ↦ exp(‖x‖²) g(x)` cancels the full Gaussian pointwise;
the modified integrand is integrable because it is the original product.
For the bounded compact-support assertion, the norm is bounded by a radius
`R` on the support, so the test is bounded in modulus by
`C exp(R²/2) exp(-‖x‖²/2)` everywhere if `C` bounds its modulus.

## Provenance and scope

This is an internal measure-theoretic helper for the standard-test spanning
step of the adjacent-rank Godement argument in H. Jacquet,
[*Archimedean Rankin–Selberg Integrals*](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
(2009, registered author-posted edition, §8.3, printed/PDF pp. 58–59).
The norm can be taken to be the Euclidean norm on the real and imaginary
matrix coordinates; the full Gaussian here has coefficient `1`, not the
coefficient `2π` of the source's normalization. The determination lemma is
derived using Mathlib's characteristic-function uniqueness, not quoted from
Jacquet. It does not supply the half-strength integrability bound in the
Godement chamber, establish spanning of the standard vectors, or prove a
Rankin–Selberg functional equation.
