# Convergence and holomorphy of the real equal-rank Rankin–Selberg integral

Module of an intermediate result of Task 7400, towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`. It proves the
one-sided statement below. The module `RealEqualDualConvergence` builds on it and proves the
two-sided statement `RealEqualPairConvergenceStatement`, which also covers the dual integral.
Authored by Worker 823. Every declaration is proved, with no axioms beyond Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

At a real place, for `n = r + 1`, a Schwartz function `Φ` on `ℝⁿ` and functions `W`, `W'` on
`GL_n(ℝ)`, the Library defines the equal-rank integral

`Ψ(s; W, W', Φ) = ∫_(N_n(ℝ) \ GL_n(ℝ)) W(g) W'(g) Φ(e_n g) |det g|^s dg`

(`ArchimedeanLocal.realEqualIntegral D W W' Φ s`, with integrand
`ArchimedeanLocal.realEqualIntegrand W W' Φ s`). The quotient measure is `D.measure` for quotient
measure data `D : RealQuotientMeasureData r`, and the integrand is evaluated at the
representative `q.out` of each coset `q`. This module proves Jacquet, *Archimedean
Rankin–Selberg integrals* (2009), Theorem 2.1(i) (p. 6: "the integrals converge for
`Re s ≫ 0`") for the integral (2.6). It also proves holomorphy of `Ψ` on the half-plane of
convergence, for Whittaker functions whose derivatives are bounded with a common growth
exponent.

## The statement

`Langlands.Global.RankinSelbergGlobal.RealEqualConvergenceStatement : Prop` says the
following. Let `r : ℕ`, `D : RealQuotientMeasureData r`, `a : ℝˣ`, `W, W' : GL_(r+1)(ℝ) → ℂ`,
and `Φ` a Schwartz function on `Fin (r + 1) → ℝ`. Assume:

1. For every list `Xs` of real `(r+1) × (r+1)` matrices, the iterated right derivative
   `RealLocalWhittaker.iteratedRightDerivative r Xs W` lies in
   `RealLocalWhittaker.regularFunctions r a`. That is, it is smooth, satisfies
   `F(u g) = realWhittakerCharacter a u · F(g)` for upper unipotent `u`, and has polynomial
   growth.
2. There is one exponent `N` such that every such derivative is bounded by
   `C_Xs · realMatrixHeight(g)^N`, with `C_Xs ≥ 0`.
3. and 4. The same two conditions hold for `W'`, with the character for `-a` in place of `a`.

Then there is a real `σ` such that the integrand `realEqualIntegrand W W' Φ s` is integrable
for `D.measure` whenever `σ < Re s`, and `s ↦ realEqualIntegral D W W' Φ s` is complex
differentiable (holomorphic) on `{s : σ < Re s}`.

The theorem `Langlands.Global.RankinSelbergGlobal.realEqualConvergence` proves it.

The pairing of `a` with `-a` matches the equal-rank packages of
`RealJacquetConventionReduction`, where `W` lies in a model for `a` and `W'` in one for `-a`.
Condition 2 is a common growth exponent for all derivatives. For Whittaker functions of a
representation this is Jacquet's Lemma 3.7 (p. 15), which gives `|ρ(X) W_v(g)| ≤ ‖g‖^M ν(dπ(X) v)`
with `M` independent of `X`. The Library's `HasPolynomialGrowth` alone gives an exponent
for each function separately, which is too weak for the gauge estimate. So the uniform
exponent is an explicit hypothesis here.

## Proof structure

The proof combines three helper modules:

- `RealIwasawaMeasure.exists_lintegral_alphaQ`: for compatible quotient measure data there are
  `κ ≥ 0` and a linear form `L` on `ℝⁿ` such that
  `∫ B(alphaQ q) dν(q) = κ ∫ exp(L x) B(x) dx` for measurable `B ≥ 0`. Here `alphaQ q` is
  the logarithm of the diagonal part of the Iwasawa decomposition of `q`.
- `RealWhittakerGauge.exists_gauge_bound`: the gauge estimate (Jacquet's Proposition 3.1, p. 16).
- `RealConvergenceAnalysis`: the exponent inequality `exponent_le`, the integrability of
  `exp(−∑|x_j|)`, and holomorphy of integrals `∫ f · exp(sℓ)` (`differentiableOn_integral_cexp_mul`).

The declarations of this module are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealEqualConvergence`, except the statement and its
proof.

### Hypothesis shapes

- `HasGauge W`: there is `N : ℕ` such that for every `M : ℕ` there is `C ≥ 0` with
  `‖W(torus y · k)‖ ≤ C · exp(−M · rootPos y + N ∑_j |y_j|)` for all `y ∈ ℝⁿ` and orthogonal
  `k`. Here `torus y = diag(exp y_j)` and `rootPos y = ∑_(i<r) max(y_i − y_(i+1), 0)`. This is
  the conclusion shape of `exists_gauge_bound`.
- `HasRapidDecay Φ`: for every `k` there is `C` with `‖x‖^k ‖Φ(x)‖ ≤ C`.

### Functions on the quotient

- `kernel W W' Φ g = W(g) W'(g) Φ(lastRow g)` and `logDet g = log |det g|`.
- `kernel_unipotent_mul`: if `W(ug) W'(ug) = W(g) W'(g)` for upper unipotent `u`, then the
  kernel is left `N`-invariant, because `lastRow (u g) = lastRow g`.
  `logDet_unipotent_mul`: `logDet` is left `N`-invariant (`det u = 1`).
- `out_eq_descend`: for a left `N`-invariant `f`, `f(q.out)` is the descended function
  `descend f` at `q`. `continuous_descend` and `continuous_descend_real`: descents of
  continuous functions are continuous (quotient topology). `continuous_logDet` and
  `continuous_kernel`: continuity on `GL_n(ℝ)`.
- `eq_torus_mul_kpart`: a left `N`-invariant `f` satisfies `f(g) = f(torus(alpha g) · kpart g)`
  (Iwasawa decomposition from `RealIwasawa`). `alpha_out`: `alpha(q.out) = alphaQ q`.
- `realEqualIntegrand_eq`: the integrand is `kernel(q.out) · exp(s · logDet(q.out))`, by
  definition of `detPower`.

### Values on `torus y · k`

- `abs_det_unitary`: `|det k| = 1` for orthogonal `k`. `logDet_torus_mul`:
  `logDet(torus y · k) = ∑_j y_j`.
- `kRow k`: the last row of `k`. `lastRow_torus_mul`: `lastRow(torus y · k) = exp(y_r) · kRow k`.
- `one_le_mul_norm_kRow`: `1 ≤ (r+1) ‖kRow k‖` (sup norm), because the row is a unit vector
  with `r + 1` entries. `exp_le_mul_norm_lastRow`: `exp(y_r) ≤ (r+1) ‖lastRow(torus y · k)‖`.

### Rapid decay along the last row

- `exists_norm_le_exp`: if `Φ` has rapid decay, `c > 0` and `K : ℕ`, there is `C ≥ 0` such that
  `exp(m) ≤ c‖x‖` implies `‖Φ(x)‖ ≤ C exp(−K max(m, 0))`. Proof: for `m ≤ 0` use the
  `k = 0` bound. For `m > 0`, `exp(Km) ≤ c^K ‖x‖^K`, and use the `k = K` bound.

### Integrability criterion

- `continuous_rootPos`; `linear_le`: `L(y) ≤ ‖L‖ ∑_j |y_j|`.
- `integrable_of_toral_bound`: take `ν`, `κ`, `L` as in `exists_lintegral_alphaQ`. Let `h` be
  an a.e. strongly measurable function on the quotient with
  `‖h(q)‖ ≤ C exp(−M rootPos y + A ∑|y_j| + t ∑ y_j − K max(y_r, 0))` at `y = alphaQ q`,
  where `C, A ≥ 0`, `(A + ‖L‖ + 1)(r+1) ≤ t`, and `M` and `K` are both at least
  `(A + ‖L‖ + 1)(r+1) + t(r+1)`. Then `h` is integrable. Proof: bound `∫⁻ ‖h‖ dν` by
  `∫⁻ B(alphaQ q) dν` with `B` the right-hand side. Rewrite it as
  `κ ∫⁻ exp(L x) B(x) dx`. By `linear_le` and `exponent_le` (with `A + ‖L‖` in place of `A`),
  `exp(L x) B(x) ≤ C exp(−∑|x_j|)`, which has finite integral.

### The main theorems

- `exists_convergence`: let `W, W'` be continuous with `W(ug)W'(ug) = W(g)W'(g)` for upper
  unipotent `u`, both satisfying `HasGauge` (with exponents `N₁`, `N₂`), and let `Φ` be
  continuous with rapid decay. Then
  `σ = (N₁ + N₂ + ‖L‖ + 1)(r+1)` works, with `L` from `exists_lintegral_alphaQ`.
  Proof: put `f(q) = kernel(q.out)` and `ℓ(q) = logDet(q.out)`. Both are continuous, as
  descents of continuous invariant functions. For real `t > σ`, let `M` be the ceiling of
  `(N₁ + N₂ + ‖L‖ + 1)(r+1) + t(r+1)`. Use the gauge bound of `W` with decay `M` and that of
  `W'` with decay `0`. Use `exists_norm_le_exp` with `c = r + 1` and `K = M`, applied at
  `x = lastRow(torus y · k)` and `m = y_r`. Write `y = alphaQ q` and `k = kpart(q.out)`.
  Then `eq_torus_mul_kpart` and `logDet_torus_mul` bound `‖f(q)‖ exp(t ℓ(q))` by
  `C₁C₂C₃ exp(−M rootPos y + (N₁+N₂) ∑|y_j| + t ∑ y_j − M max(y_r, 0))`. So
  `integrable_of_toral_bound` makes `‖f‖ exp(tℓ)` integrable for every `t > σ`. For complex
  `s` with `Re s > σ` the integrand `f · exp(sℓ)` has norm `‖f‖ exp(Re(s) ℓ)`
  (`norm_cexp_mul_ofReal`), so it is integrable. Holomorphy is
  `differentiableOn_integral_cexp_mul` applied to `f` and `ℓ`.
- `realWhittakerCharacter_mul_neg`: `realWhittakerCharacter a u · realWhittakerCharacter (−a) u = 1`,
  since both are values of `x ↦ exp(2πi a x)` and `x ↦ exp(−2πi a x)` at the same point.
- `hasRapidDecay_schwartz`: Schwartz functions have rapid decay (`SchwartzMap.decay` with zero
  derivatives).
- `exists_convergence_of_regular`: the statement's conclusion under its hypotheses. The empty
  list gives `W ∈ regularFunctions r a` and `W' ∈ regularFunctions r (−a)`. Smoothness gives
  continuity, the two character laws and `realWhittakerCharacter_mul_neg` give the
  `N`-invariance of `W W'`, and `exists_gauge_bound` gives `HasGauge` for both. Then apply
  `exists_convergence`.
- `realEqualConvergence : RealEqualConvergenceStatement` is `exists_convergence_of_regular`.

## Relation to the literature

Jacquet (2009) proves convergence for Whittaker functions of the induced representations
`I_(σ,u)` (Theorem 2.1(i)). The gauge estimate is his Proposition 3.1 (pp. 15–16), and the
equal-rank convergence argument is in §5.1 (p. 32), using the majorant of Lemma 3.5, (3.10)
(p. 14). In the proof of Lemma 3.5 Jacquet writes `g = a k` on `N \ G` and
`dg = J(a) da dk` with a Jacobian character `J(a)` whose value he leaves symbolic; after
integrating over `K` he applies the positive-character estimate of Lemma 3.4 (pp. 13–14).
The Lean proof also works in Iwasawa coordinates on the measure side, but derives the
density differently: `exists_lintegral_alphaQ` (module `RealIwasawaMeasure`) pushes the
quotient measure forward along the logarithmic toral Iwasawa coordinate `alphaQ`. Applying
the compatibility (Weil formula) of the quotient measure with Haar measures on `G` and `N`
to lifts `g ↦ φ(alpha g) β(npart g)` built from the toral and unipotent Iwasawa coordinates
and to their torus translates shows that this pushforward is quasi-invariant under
translations. Haar uniqueness on `ℝⁿ` then makes it a nonnegative multiple of
`exp(L x) dx` for a linear form `L`. The proof of `exists_convergence` uses this formula with
`y = alphaQ q`. The linear form `L` is left unspecified, so the convergence abscissa `σ` depends on the unknown
`‖L‖`; only its existence is claimed. The statement replaces "Whittaker function of `I_(σ,u)`" by the
explicit regularity and uniform-growth hypotheses above, which are the properties the proof
uses.
