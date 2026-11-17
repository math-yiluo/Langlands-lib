# Landau's theorem for Laplace transforms of nonnegative functions

Module `Langlands.Analysis.LandauMellin`, namespace `Langlands.LandauMellin`.

This is an analysis helper module: it contains definitions of transforms and theorems
about them, but no `Prop`-valued statement definitions. It was written for the self-pair
Rankin–Selberg continuation (Task 6821). Its global zeta integrals are Mellin transforms
`∫ F(g) |det g|^s dg` of nonnegative functions `F`, so they are two-sided Laplace transforms
in the variable `log |det g|`. Everything here holds for an arbitrary measure space `(X, μ)`.
Nothing in it is specific to automorphic forms.

## Sources

* D. V. Widder, *The Laplace Transform*, Princeton Mathematical Series 6, Princeton
  University Press, 1941. Chapter II, §5, Theorem 5b (printed p. 58): if the determining
  function `α(t)` is monotonic, the real point of the axis of convergence of
  `∫₀^∞ e^{-st} dα(t)` is a singularity of the function the integral represents. The proof
  (pp. 58–59) expands the function in a Taylor series at a real point to the right of the
  abscissa. Because the terms are nonnegative, summation and integration can be
  interchanged at a real point to the left. Chapter VI, §1, formula (4) (printed
  pp. 237–238) splits a two-sided (bilateral) transform into two one-sided transforms, one
  of them evaluated at `-s`.
  (Page numbers are those of the 1946 printing, archive.org item `dli.ernet.206074`, where
  printed page = PDF page − 10.)
* G. H. Hardy and M. Riesz, *The General Theory of Dirichlet's Series*, Cambridge Tracts
  18, 1915 (registered as `hardy-riesz-1915-dirichlet-series`). Theorem 10, p. 10, is
  Landau's theorem for Dirichlet series with nonnegative coefficients, proved the same way.

The Lean module states and proves the same theorem for abstract measure spaces. A
Laplace–Stieltjes integral `∫ e^{-st} dα(t)` with nondecreasing `α` is the case
`X = [0, ∞)`, `μ = dα`, `c = 1`, `ℓ = t`. What matters is that `dα` is a nonnegative
measure, that is, that `α` is monotonic. Nonnegativity of `α` itself would not suffice: for
`α(t) = 1 − cos t` the transform is `1/(s² + 1)` on `Re s > 0`, so its abscissa of
convergence is `0`, yet `s = 0` is a regular point. A Dirichlet series `∑ aₙ e^{-λₙ s}` with
`aₙ ≥ 0` is the case of counting measure on `ℕ`. Following Landau's theorem as these
sources use it, the Lean statements are about absolute convergence, meaning
integrability, rather than about conditional convergence of improper integrals. For
nonnegative integrands the two notions agree.

## Definitions

* `kernel c ℓ s x = c x * exp (-ℓ x * s)` and the one-sided transform
  `transform μ c ℓ s = ∫ kernel c ℓ s x dμ`. The function `c` plays the role of the
  density `dα`, and `ℓ` plays the role of the frequency `t`, or `λₙ` for Dirichlet series.
* `IntegrableAt μ c ℓ σ`: integrability of the real function `c x * exp (-ℓ x * σ)`, that
  is, absolute convergence at the real point `σ`.
* `derivCoeff c ℓ m x = c x * (-ℓ x)^m`: the coefficients of the `m`-th derivative.
* `taylorTerm c ℓ δ a n x = c x * (δ ℓ x)^n / n! * exp (-ℓ x * a)`: the `n`-th Taylor term
  at the real point `a`, evaluated at `a - δ`, before integration.
* `bilateral μ f u s = ∫ f x * exp (s * u x) dμ`: the two-sided transform with real phase
  `u`. A Mellin transform `∫ F(g) |det g|^s dg` is `bilateral` with `u = log |det g|`.

## Main results

All results are under almost-everywhere hypotheses `0 ≤ c`, `0 ≤ ℓ` (one-sided) or `0 ≤ f`
(two-sided), together with almost-everywhere strong measurability.

### One-sided transforms

* `IntegrableAt.mono`: absolute convergence at `σ` implies it at every `σ' ≥ σ`.
* `IntegrableAt.mul_pow`: absolute convergence at `σ` implies absolute convergence of the
  coefficients `c ℓ^m` at every `σ' > σ`. The proof uses `y^m e^{-ty} ≤ m!/t^m`.
* `hasDerivAt_transform`, `iteratedDeriv_transform`: if the transform converges absolutely
  at every real `σ > σc`, then on `σc < Re s` the derivative of the transform with
  coefficients `c (-ℓ)^m` is the transform with coefficients `c (-ℓ)^(m+1)`. Hence the
  `m`-th iterated derivative is the transform with coefficients `derivCoeff c ℓ m`. This is
  differentiation under the integral sign, using
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
* `differentiableOn_transform`: under the same hypothesis the transform is holomorphic on
  `σc < Re s`.
* `integrableAt_sub_of_taylor` (the Taylor step): let `σc < a` and suppose the transform
  converges absolutely at every real `σ > σc`. Let `g` be holomorphic on the disc of radius
  `R` about `a` and equal to the transform on the part of the disc where `σc < Re s`. Then
  the transform converges absolutely at `a - δ` for every `0 ≤ δ < R`.
* `exists_integrableAt_lt`: if the transform converges absolutely to the right of `σc` and
  agrees there with a function holomorphic on a disc about `σc`, it converges absolutely at
  some real point `σ < σc`.
* `integrableAt_of_abscissa`: the infimum argument. Suppose the transform converges
  absolutely at some point, and every abscissa `σc > σ₀` (a point where it converges
  absolutely to the right) can be pushed further left. Then it converges absolutely at
  every real `σ > σ₀`.
* **`integrableAt_of_differentiableOn`** (Landau's theorem; Widder, Theorem II.5b): suppose
  the transform converges absolutely at the real point `σ₁`, and agrees on `σ₁ < Re s`
  with a function `g` holomorphic on `σ₀ < Re s`. Then it converges absolutely at every
  real `σ > σ₀`.

Also: `eqOn_halfPlane` is the identity theorem on a right half-plane, and
`ball_subset_halfPlane` says that the disc of radius `σc - σ₀` about `σc` lies in
`σ₀ < Re s`.

### Two-sided transforms

* `integrable_bilateral`: absolute convergence at `s` follows from integrability of
  `f x * exp (Re s * u x)`.
* `bilateral_eq_add` (Widder VI §1 (4)): the two-sided transform is the sum of the
  one-sided transform over `{u < 0}` with frequency `-u` and the one-sided transform over
  `{u ≥ 0}` with frequency `u`, evaluated at `-s`.
* `integrableOn_compl`, `differentiable_compl`: if the two-sided transform converges
  absolutely at every real `σ > σ₁`, then on `{u ≥ 0}` it converges absolutely at every
  real point. The one-sided transform over `{u ≥ 0}` at `-s` is therefore entire in `s`.
* `differentiableOn_bilateral`: if the two-sided transform converges absolutely at every
  real `σ > σ₀`, it is holomorphic on `σ₀ < Re s`.
* **`integrable_of_differentiableOn`** (Landau's theorem for two-sided transforms): suppose
  `∫ f x * exp (s * u x) dμ` with `f ≥ 0` converges absolutely at every real `σ > σ₁`, and
  agrees on `σ₁ < Re s` with a function holomorphic on `σ₀ < Re s`. Then it converges
  absolutely at every real `σ > σ₀`.

## Proof outline (as implemented)

**Taylor step.** Let `a > σc` be real. The function `g` agrees with the transform near
`a`, so the iterated derivatives of `g` at `a` are the transforms with coefficients
`c (-ℓ)^n` (`iteratedDeriv_transform`). The Taylor series of `g` at `a` converges on the
whole disc where `g` is holomorphic (`Complex.hasSum_taylorSeries_on_ball`). Evaluate it at
`a - δ`. By `taylor_coeff_eq`, the `n`-th term equals `∫ taylorTerm c ℓ δ a n`, so the real
series `∑ₙ ∫ taylorTerm …` converges. Pointwise, `∑ₙ taylorTerm c ℓ δ a n x` is
`c x e^{δ ℓ x} e^{-ℓ x a} = c x e^{-ℓ x (a - δ)}`, the exponential series. All terms are
nonnegative, so monotone convergence (`lintegral_tsum`) gives
`∫⁻ c e^{-ℓ (a-δ)} = ∑ₙ ∫⁻ taylorTerm … < ∞`. This is the interchange of sum and integral
in Widder's proof.

**Infimum argument.** Let `σ₂ > σ₀` and suppose the transform does not converge absolutely
at `σ₂`. Let `σc` be the infimum of the real points of absolute convergence. Since the set
of such points is upward closed (`IntegrableAt.mono`), `σc ≥ σ₂ > σ₀`. The transform
converges absolutely at every `σ > σc`. By the identity theorem (`eqOn_halfPlane`) it
agrees with `g` on `σc < Re s`. Since `g` is holomorphic on the disc of radius `σc - σ₀`
about `σc`, `exists_integrableAt_lt` gives a point of absolute convergence below `σc`. This
contradicts the definition of the infimum.

**Two-sided case.** Split `X = {u < 0} ∪ {u ≥ 0}`. On `{u ≥ 0}` the factor `exp (σ u)` is
increasing in `σ`, so absolute convergence at large `σ` gives absolute convergence at every
real `σ`. The corresponding one-sided transform at `-s` is then entire. Subtracting it from
`g` gives a function holomorphic on `σ₀ < Re s` that agrees with the one-sided transform
over `{u < 0}` with nonnegative frequency `-u`. The one-sided Landau theorem applies to it.
The two pieces are then glued back together (`IntegrableOn.union`).
