# Landau's theorem for general Dirichlet series with nonnegative coefficients

Lean module: `Langlands.Analysis.LandauDirichlet`, namespace
`Langlands.GeneralDirichlet`. It imports only Mathlib. It is a helper for the
proof of `Langlands.Global.CuspidalPairAbsoluteConvergenceReductionStatement`
(module `Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceProof`). Neither Mathlib nor the Library had a Landau-type theorem: a search
for `Landau`, `abscissaOfAbsConv` and nonnegative coefficients found none.

## Setting

The index type `ι` is arbitrary. The coefficients are real, `c : ι → ℝ`, and
so are the exponents, `ℓ : ι → ℝ`. Every theorem below assumes `c i ≥ 0` and
`ℓ i ≥ 0`.

- `term c ℓ i s = c i * exp (-ℓ i * s)` for `s : ℂ`.
- `series c ℓ s = ∑' i, term c ℓ i s`.
- `SummableAt c ℓ σ` (for real `σ`): `i ↦ c i * exp (-ℓ i * σ)` is summable.
  The terms are nonnegative, so this is absolute convergence. For complex `s`
  with `Re s ≥ σ`, the norms `‖term c ℓ i s‖ = c i * exp (-ℓ i * Re s)` are then
  summable too.
- `derivCoeff c ℓ m i = c i * (-ℓ i) ^ m`, the coefficients of the `m`-th
  derivative.

With `ℓ i = log λ_i` this is the series `∑ c_i λ_i^(-s)`. With
`ℓ i = (n + 1) log q_v` it is the double series of Jacquet–Shalika I, (5.3.3).
That is how the consumer module `CuspidalPairAbsoluteConvergenceProof` uses it.

## Main theorems

```lean
theorem Langlands.GeneralDirichlet.summableAt_of_differentiableOn
    (hℓ : ∀ i, 0 ≤ ℓ i) (hc : ∀ i, 0 ≤ c i) {σ₀ σ₁ : ℝ} (h₁ : SummableAt c ℓ σ₁)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g {s : ℂ | σ₀ < s.re})
    (hgD : ∀ s : ℂ, σ₁ < s.re → g s = series c ℓ s) :
    ∀ σ, σ₀ < σ → SummableAt c ℓ σ
```

**Landau's theorem.** Suppose the series converges at some real point `σ₁` and
agrees, on `σ₁ < Re s`, with a function holomorphic on `σ₀ < Re s`. Then it
converges at every real `σ > σ₀`.

```lean
theorem Langlands.GeneralDirichlet.summableAt_of_exp
    (hc : ∀ i, 0 ≤ c i) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (hℓ₀le : ∀ i, ℓ₀ ≤ ℓ i)
    {σ₀ σ₁ : ℝ} (h₁ : SummableAt c ℓ σ₁) {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L {s : ℂ | σ₀ < s.re})
    (hLD : ∀ s : ℂ, σ₁ < s.re → L s = Complex.exp (series c ℓ s)) :
    ∀ σ, σ₀ < σ → SummableAt c ℓ σ
```

**The exponential form.** The conclusion is the same, but only `exp` of the
series is assumed to continue holomorphically. The exponents must be bounded
below by some `ℓ₀ > 0`.

## Proof

1. **Termwise calculus** (`hasDerivAt_term`, `hasSum_deriv_series`,
   `iteratedDeriv_series`, `differentiableOn_series`, `hasDerivAt_series`).
   Suppose the series converges at every `σ > σc`. Multiplying the coefficients
   by `ℓ i ^ m` keeps convergence strictly to the right (`SummableAt.mul_pow`),
   because `ℓ ^ m e^(-tℓ) ≤ m! / t ^ m` (`Real.pow_div_factorial_le_exp`). On
   every half-plane `σ' < Re s` with `σ' > σc`, the terms and their derivatives
   are bounded by summable constants. So the series is holomorphic on
   `σc < Re s` (Mathlib's `differentiableOn_tsum_of_summable_norm`). It can be
   differentiated termwise (`hasSum_deriv_of_summable_norm`), and its `m`-th
   derivative is `series (derivCoeff c ℓ m) ℓ`.
2. **The Taylor step** (`summableAt_sub_of_taylor`). Let `g` be holomorphic on
   the ball of radius `R` about a real `a > σc`, and equal to the series near
   `a`. By Mathlib's `Complex.hasSum_taylorSeries_on_ball`, the Taylor series of
   `g` at `a` converges at `a - δ` for `0 ≤ δ < R`. Its coefficients are
   `iteratedDeriv n (series c ℓ) a / n!` (step 1). At `a - δ` the `n`-th term
   is `∑' i c_i (δ ℓ_i) ^ n / n! e^(-ℓ_i a)` (`taylor_coeff_eq`), a sum of
   nonnegative reals. By Tonelli for nonnegative double series
   (`summable_prod_of_nonneg`, both orders), the rows
   `∑ₙ c_i (δ ℓ_i) ^ n / n! e^(-ℓ_i a) = c_i e^(-ℓ_i (a - δ))` are summable. So
   the series converges at `a - δ`.
3. **Landau at the abscissa** (`exists_summableAt_lt`). Suppose the series
   converges to the right of `σc` and agrees there with a function holomorphic
   on a disc of radius `ε` about `σc`. Apply step 2 with `a = σc + ε/4`,
   `R = ε/2` and `δ = 3ε/8`. The series then converges at `σc - ε/8`.
4. **The infimum argument** (`summableAt_of_abscissa`). Suppose the series
   diverges at some `σ₂ > σ₀`. Let `σc ≥ σ₂` be the infimum of the real points
   of convergence, and suppose that no `σc > σ₀` admits convergence to its left.
   That is a contradiction.
5. **Landau's theorem.** Let `σc > σ₀` be such that the series converges to the
   right of `σc`. By the identity theorem on the convex half-plane
   (`eqOn_halfPlane`), `g` equals the series on `σc < Re s`. The disc of radius
   `σc - σ₀` about `σc` lies in `σ₀ < Re s` (`ball_subset_halfPlane`), so step 3
   applies.
6. **The exponential form.** Let `σc > σ₀` be as in step 5. By the identity
   theorem, `L = exp ∘ series` on `σc < Re s`. For real `σ > σc` the series is
   a nonnegative real number, so `‖L σ‖ ≥ 1`. By continuity, `‖L σc‖ ≥ 1`, so
   `L` does not vanish on a disc about `σc`. On that disc `-L'/L` is
   holomorphic. On `σc < Re s` it equals `-(series)' = series (c ℓ) ℓ`
   (`hasDerivAt_series`). Step 3, applied to the coefficients `c_i ℓ_i ≥ 0`,
   gives convergence of `∑ c_i ℓ_i e^(-ℓ_i σ)` at some `σ < σc`. Since
   `ℓ_i ≥ ℓ₀ > 0`, `c_i ≤ c_i ℓ_i / ℓ₀`, so the original series converges
   there too. Step 4 concludes.

## Sources and provenance

- G. H. Hardy and M. Riesz, *The General Theory of Dirichlet's Series*,
  Cambridge Tracts in Mathematics and Mathematical Physics 18, Cambridge
  University Press, 1915. Registered source `hardy-riesz-1915-dirichlet-series`
  (project literature file, SHA256
  `506e09782db969bbe3e2724f3a528df9b59a8bec9437141761ec9612e177cfad`; scan of
  the 1915 edition, archive.org `cu31924060184441`; printed page = PDF page
  − 16).
  - §1, p.1 (PDF 17): the series `f(s) = ∑ a_n e^(-λ_n s)` with real
    increasing `λ_n → ∞`.
  - Theorem 10, p.10 (PDF 26): "If all the coefficients of the series are
    positive or zero, then the real point of the line of convergence is a
    singular point of the function represented by the series." The proof
    expands `f` in its Taylor series at a real point to the right of the line.
    The radius of convergence exceeds the distance to the line. Inverting the
    resulting double series of positive terms shows convergence to the left
    of the line.
- H. Jacquet and J. A. Shalika, *On Euler products and the classification of
  automorphic representations I*, Amer. J. Math. 103 (1981), registered as
  `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`
  (printed page = PDF page + 498). Proof of Theorem (5.3), p.556 (PDF 58).
  `f(s)` of (5.3.3) is a Dirichlet series with nonnegative coefficients. If the
  real point `a` of its line of convergence were `> 1`, then `L_S(s, π × π̃)`
  would tend to a finite limit `≥ 1` at `a` by Lemma (5.2). So near `a`,
  `log L_S = f`, which contradicts "a well-known theorem on Dirichlet series"
  that `a` is a singularity of `f`.

`summableAt_of_differentiableOn` is Hardy–Riesz Theorem 10 in contrapositive
form. A function holomorphic on `σ₀ < Re s` has no singular point there, so the
real point of the line of convergence is at most `σ₀`. The proof is the one in
Hardy–Riesz. Two things differ from the source. The index set is arbitrary
rather than an increasing sequence `λ_n → ∞`. And convergence means summability
of the nonnegative terms, which is absolute convergence. With nonnegative
coefficients, Hardy–Riesz's ordinary convergence of `∑ a_n e^(-λ_n σ)` at a
real point is the same thing.

`summableAt_of_exp` is the form in which Jacquet–Shalika apply the theorem at
p.556. The step from `L = exp f` to the singularity of `f` follows them. The
limit at the real point is at least 1, so `L` does not vanish near it.
Jacquet–Shalika then take `log L`. This module takes the logarithmic derivative
`-L'/L` instead, and applies the local form of Landau's theorem (step 3) to the
series of `c_i ℓ_i`. This avoids choosing a holomorphic logarithm.

## What is not asserted

- Nothing about ordinary (non-absolute) convergence of series with signed or
  complex coefficients, the abscissa of convergence as a Mathlib
  `LSeries.abscissaOfAbsConv`, or growth of the series.
- Nothing about the boundary `Re s = σ₀` itself.

## Lean checks

The module was compiled with no errors or warnings. Both main theorems depend only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.
