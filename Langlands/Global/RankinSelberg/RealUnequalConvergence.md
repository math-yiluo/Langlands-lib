# Convergence and holomorphy of the real unequal-rank Rankin–Selberg integral

Module of an intermediate result of Task 7400, towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`. Authored by
Worker 823. Every declaration is proved, with no axioms beyond Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

Let `t < r`, `n = r + 1` and `m = t + 1`. The unequal-rank integral at a real place is

`Ψ(s; W, W') = ∫_(N_m \ GL_m(ℝ)) W(diag(g, 1_(n−m))) W'(g) |det g|^(s − (n−m)/2) dg`

(`ArchimedeanLocal.realUnequalIntegral h D W W'`, with integrand
`ArchimedeanLocal.realUnequalIntegrand h W W' s` and the quotient measure of `D`). This module
proves that the integral converges absolutely and is holomorphic on a right half-plane. These
are the first and third conjuncts of the Library's package `RealJacquet.UnequalEquation`
(module `RealJacquetConventionReduction`). The conjuncts for the dual integral are not treated
here.

## The statement

`Langlands.Global.RankinSelbergGlobal.RealUnequalConvergenceStatement : Prop` says the
following. Let `r, t : ℕ` with `h : t < r`, let `D : RealQuotientMeasureData t`, `a : ℝˣ`,
`W : GL_(r+1)(ℝ) → ℂ` and `W' : GL_(t+1)(ℝ) → ℂ`. Assume:
- every iterated right derivative of `W` lies in `RealLocalWhittaker.regularFunctions r a`;
- for some `N`, every iterated right derivative of `W` is bounded by
  `C · realMatrixHeight(g)^N`, where `C` may depend on the derivative but `N` may not;
- every iterated right derivative of `W'` lies in
  `RealLocalWhittaker.regularFunctions t (−a)`;
- the same common-exponent growth bound holds for `W'`.

Then there is a real `σ` such that the integrand `realUnequalIntegrand h W W' s` is integrable
for `D.measure` whenever `σ < Re s`, and `realUnequalIntegral h D W W'` is complex
differentiable on `{s : σ < Re s}`.

The theorem `Langlands.Global.RankinSelbergGlobal.realUnequalConvergence` proves it. The
hypotheses have the same form as in `RealEqualConvergenceStatement` (module
`RealEqualConvergence`), with `W` and `W'` on groups of different ranks.

## Proof structure

The declarations below are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealUnequalConvergence`. The proof follows the
equal-rank proof of `RealEqualConvergence.exists_convergence`. There the Schwartz function
supplies decay when the last toral coordinate tends to `+∞`. Here the gauge estimate of `W`
at `diag(g, 1)` supplies that decay.

### Padding

- `padVec r y` is the vector `y ∈ ℝ^(t+1)` followed by `r − t` zeros. `extVec y` is the same
  extension to all natural indices; it is used to compare sums over `Fin (t+1)`, `Fin r` and
  `Fin (r+1)` as sums over ranges of natural numbers.
- `padGL_torus`: `diag(torus y, 1) = torus(padVec r y)`, entry by entry from the Library's
  `UnequalAnalytic.padGL_apply`.
- `padGL_mem_unitary`, `padUnitary`: for orthogonal `k`, `diag(k, 1)` is orthogonal. Its
  transpose is `diag(k⁻¹, 1)`, because `k⁻¹ = ᵗk`, and padding is multiplicative.
- `rootPos_padVec`: `rootPos(padVec r y) = rootPos y + max(y_t, 0)`. The simple-root
  coordinates of `(y, 0, …, 0)` are those of `y`, then `y_t − 0`, then zeros.
- `sum_abs_padVec`: `∑_j |(padVec r y)_j| = ∑_j |y_j|`.
- `pad_gauge`: if `W` satisfies the gauge estimate `HasGauge` (module `RealEqualConvergence`),
  then there is `N` such that for every `M` there is `C ≥ 0` with

  `‖W(diag(torus y · k, 1))‖ ≤ C · exp(−M · rootPos y + N ∑_j |y_j| − M · max(y_t, 0))`

  for all `y` and orthogonal `k`. Proof: `diag(torus y · k, 1) = torus(padVec r y) · diag(k, 1)`;
  apply the gauge bound of `W` there and use the two previous lemmas.

### The Whittaker character on padded unipotent matrices

- `padGL_mem_upperUnipotent`: `diag(u, 1)` is upper unipotent if `u` is.
- `realWhittakerCharacter_padGL`: `ψ_a(diag(u, 1)) = ψ_a(u)` for every `u`. The superdiagonal of
  `diag(u, 1)` consists of the superdiagonal of `u`, followed by zeros.

### Convergence and holomorphy

- `kernel hp W W' g = W(diag(g, 1)) · W'(g)`; `continuous_kernel` uses the Library's
  `UnequalAnalytic.continuous_padGL`.
- `exists_convergence`: let `W` and `W'` be continuous, let the kernel be invariant under left
  multiplication by upper unipotent matrices of `GL_(t+1)(ℝ)`, and let `HasGauge W` and
  `HasGauge W'` hold. Then the conclusion of the statement holds. Proof:
  1. As in the equal-rank case, the kernel and `logDet` descend to continuous functions `f`, `ℓ`
     on `N_(t+1) \ GL_(t+1)(ℝ)`. At a class `q` with toral coordinate `y = alphaQ q` and
     orthogonal part `k`, `f q` is the kernel at `torus y · k` and `ℓ q = ∑_j y_j`.
  2. `exists_lintegral_alphaQ` (module `RealIwasawaMeasure`) gives `κ` and a linear form `L` such
     that integrating against the quotient measure, in the coordinate `alphaQ`, is integrating
     against `κ exp(L x) dx`.
  3. Let `N1` be the exponent from `pad_gauge` and `N2` that of `W'`. Put
     `σ0 = (N1 + N2 + ‖L‖ + 1)(t + 1)`. For `τ > σ0` choose `M ≥ (N1 + N2 + ‖L‖ + 1)(t + 1) + τ(t + 1)`.
     The bound of `pad_gauge` for this `M`, times the bound of `W'` with no decay, gives

     `‖f q‖ exp(τ ℓ q) ≤ C exp(−M rootPos y + (N1 + N2) ∑|y_j| + τ ∑ y_j − M max(y_t, 0))`.

     The criterion `RealEqualConvergence.integrable_of_toral_bound` then shows that
     `‖f‖ exp(τ ℓ)` is integrable.
  4. Put `c = (r − t)/2` and `f' = f · exp(−c ℓ)`. Then the integrand at `s` is
     `f' · exp(s ℓ)`, and `‖f'‖ exp(τ ℓ) = ‖f‖ exp((τ − c) ℓ)`. So this is integrable for
     `τ > σ0 + c`. Take `σ = σ0 + c`. Integrability of the integrand follows by comparison.
     Holomorphy follows from `RealConvergenceAnalysis.differentiableOn_integral_cexp_mul`.
- `exists_convergence_of_regular`: the statement's conclusion under its hypotheses. The empty
  derivative list gives `W ∈ regularFunctions r a` and `W' ∈ regularFunctions t (−a)`.
  Smoothness gives continuity. The two character laws, `padGL_mem_upperUnipotent`,
  `realWhittakerCharacter_padGL` and `RealEqualConvergence.realWhittakerCharacter_mul_neg` give
  invariance of the kernel. `RealWhittakerGauge.exists_gauge_bound` gives `HasGauge W` and
  `HasGauge W'`.
- `realUnequalConvergence : RealUnequalConvergenceStatement` is
  `exists_convergence_of_regular`.

## Relation to the literature

Jacquet, *Archimedean Rankin–Selberg integrals* (2009), proves convergence of `Ψ(s; W, W')` for
`Re s ≫ 0` in §5.1 (p. 32), case `n > n'`. He bounds `W(diag(g, 1))` by a power of the gauge
`ξ_h,n`, as in the majorization of Proposition 3.1 (pp. 15–16). He observes that, up to a
scalar, `ξ_h,n(diag(g, 1)) = ξ_i,m(g)`, which dominates a power of `ξ_s,m(g)`, and concludes
with Lemma 3.5, integral (3.9) (p. 14). In the
formalization the analogous step is `rootPos_padVec`. Jacquet's majorant is replaced by the
exponent inequality `RealConvergenceAnalysis.exponent_le` in logarithmic toral coordinates,
used through `integrable_of_toral_bound`. Holomorphy in the region of convergence comes from
differentiation under the integral sign. In the proof of Lemma 3.5 (p. 14) Jacquet writes
`dg = J(a) da dk` with a Jacobian character `J(a)` left symbolic and applies Lemma 3.4.
Here the quotient measure is handled as in `RealEqualConvergence`: the pushforward of the
quotient measure along the logarithmic toral Iwasawa coordinate `alphaQ` is shown, by the
Weil formula and Haar uniqueness on `ℝᵐ`, to be `κ exp(L x) dx` for a linear form `L` left
unspecified (module `RealIwasawaMeasure`), so `σ` is only shown to exist. Jacquet's
hypothesis that `W` and `W'` are Whittaker functions of
induced representations is replaced by the explicit regularity and common-exponent growth
hypotheses, which are the properties the proof uses (his Lemma 3.7, p. 15).
