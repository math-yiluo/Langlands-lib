# Convergence and holomorphy of the real unequal-rank block integral

Helper module of an intermediate result towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`. Every declaration is proved, with no axioms beyond Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

Let `t < r`, `n = r + 1`, `m = t + 1` and `d = r − (t + 1)`. The Library's block integral
(`ArchimedeanLocal.blockIntegral`) is

`Ψ_(n−m−1)(s; V, V') = ∫_(N_m \ GL_m(ℝ)) ∫_(M_(d×m)(ℝ)) V(rect(g, x)) V'(g) |det g|^(s−(n−m)/2) dx dg`,

with `rect(g, x) = rectangularPoint h g x = [[g, 0, 0], [x, 1_d, 0], [0, 0, 1]]`, the
rectangular variable integrated first for the product measure of an additive Haar measure `ν`
on `ℝ` (`rectangularMeasure ν d m`), and the kernel `blockKernel`. The dual side of the
unequal-rank functional equation is this integral for `V = ρ(w_(n,m)) W̃` and `V' = W̃'`.
This module proves convergence and holomorphy for general `V`, `V'` under explicit
hypotheses. The module `RealUnequalPairConvergence` applies it.

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealUnequalDualConvergence`.

## The gauge at the rectangular point

- `kpart_unipotent_mul`: the orthogonal Iwasawa coordinate is left invariant under the upper
  unipotent group.
- `gauge_any`: if `‖V(u g)‖ = ‖V(g)‖` for upper unipotent `u` and `V` satisfies `HasGauge`
  (module `RealEqualConvergence`), then for every `M` there is `C` with
  `‖V(g)‖ ≤ C exp(−M rootPos(α(g)) + N ∑_j |α_j(g)|)` for all `g`, where `α = RealIwasawa.alpha`.
  Write `g = npart g · (torus(α g) · kpart g)` and drop the unipotent factor.
- `rootPos_cast`, `sum_abs_cast`: both quantities are unchanged under the cast of indices along
  an equality of sizes.
- `rect_size`, `rectangularPoint_eq`: `rectangularPoint h g x` is the reindexing of
  `RealRectangularIwasawa.rect g x` along `t + 1 + d + 1 = r + 1`.
- `rect_bound`: under the hypotheses of `gauge_any` there is `N` such that for every `M` there is
  `C ≥ 0` with

  `‖V(rect(torus y · k, x))‖ ≤ C exp(−M (∑_j max(y_j, 0) + m log(1 + S)/2) + N (∑_j |y_j| + (m + d) log(1 + S)))`

  for all `y`, orthogonal `k` and `x`, where `S = ∑ x_(lp)²`. Proof: apply `gauge_any` with
  `(m + 2md) M`, use `RealIwasawa.alpha_reindex_finCongr`, and the estimates `decay_le` and
  `sum_abs_le` of `RealRectangularIwasawa`.

## Elementary estimates

- `coord_le`, `sum_coord_le`: if `A ≥ 0`, `τ ≥ A + 1` and `M ≥ A + τ + 1`, then
  `−M ∑ max(y_j, 0) + A ∑ |y_j| + τ ∑ y_j ≤ −∑ |y_j|`, coordinate by coordinate.
- `rectDecay x = ∏_(l,p) (1 + x_(lp)²)⁻¹`. `exp_neg_mul_log_le`: if `κ ≥ md`, then
  `exp(−κ log(1 + S)) ≤ rectDecay x`, since `∏_(l,p) (1 + x_(lp)²) ≤ (1 + S)^(md)`.
- `integrable_inv_one_add_sq_haar`, `sigmaFinite_haar`: every additive Haar measure on `ℝ` is a
  multiple of Lebesgue measure (Mathlib's `isAddLeftInvariant_eq_smul_of_regular`), so it is
  σ-finite and `(1 + v²)⁻¹` is integrable for it. `sigmaFinite_rect`, `integrable_rectDecay`: the
  rectangular measure is σ-finite and `rectDecay` is integrable for it, as a product of
  one-variable integrable functions (Mathlib's `Integrable.fintype_prod`).
- `integrable_exp_comp_alphaQ`: if integration against a measure on the quotient, in the toral
  coordinate `alphaQ`, is integration against `κ exp(L x) dx` (the output of
  `RealIwasawaMeasure.exists_lintegral_alphaQ`), and `L y + E(y) ≤ −∑ |y_j|` with `E` continuous,
  then `exp(E ∘ alphaQ)` is integrable.

## The main theorem

- `bkernel h V V' (g, x) = V(rect(g, x)) V'(g)`; `continuous_rectangularPoint` uses the Library's
  `continuous_lowerBlockLocalization` and `reindexContinuous`.
- `exists_dual_convergence`: let `V` and `V'` be continuous, let `‖V(u g)‖ = ‖V(g)‖` for upper
  unipotent `u` of `GL_n(ℝ)`, let `bkernel h V V' (u g, x) = bkernel h V V' (g, x)` for upper
  unipotent `u` of `GL_m(ℝ)`, and let `HasGauge V` and `HasGauge V'` hold. Then for every
  quotient measure data `D` and every additive Haar measure `ν` there is `σ` such that:
  1. for `Re s > σ`, `p ↦ blockKernel realNormalizedAbs h V V' s p.1 p.2` is integrable for
     `D.measure.prod (rectangularMeasure ν d m)`;
  2. `blockIntegral realNormalizedAbs D.measure ν h V V'` is complex differentiable on
     `{s : σ < Re s}`.

  Proof:
  1. The orthogonal coordinate descends to a continuous `kQ` on the quotient. So
     `sec(q) = torus(alphaQ q) · kQ(q)` is a continuous section, and by the invariance of the
     kernel `f(q, x) = bkernel(q.out, x) = bkernel(sec q, x)`. In particular `f` is continuous
     on the product. As in `RealEqualConvergence`, `ℓ(q) = log |det q.out| = ∑_j alphaQ(q)_j`.
  2. For `τ ≥ A + 1`, `A = N1 + N2 + ‖L‖`, choose
     `M ≥ A + τ + 1 + 2 N1 (m + d) + 2md`. With `rect_bound` for `V` and the bound of `V'` with
     no decay,

     `‖f(q, x)‖ exp(τ ℓ(q)) ≤ C exp(E(alphaQ q)) rectDecay(x)`,

     where `E(y) = −M ∑ max(y_j, 0) + (N1 + N2) ∑ |y_j| + τ ∑ y_j` satisfies
     `L y + E(y) ≤ −∑ |y_j|` by `sum_coord_le`. The factor of `log(1 + S)` left over is at most
     `exp(−md log(1 + S))`, which `exp_neg_mul_log_le` bounds by `rectDecay`.
  3. The bound is a product of an integrable function of `q` and an integrable function of `x`,
     so it is integrable on the product (Mathlib's `Integrable.mul_prod`). With
     `c = (r − t)/2` and `σ = A + 1 + c`, the block kernel at `s` is
     `f(p) exp((s − c) ℓ(p.1))`. Its norm is `‖f(p)‖ exp((Re s − c) ℓ(p.1))`, which gives
     integrability.
  4. For holomorphy, the inner integral is pulled out:
     `blockIntegral(s) = ∫ F(q) exp(s ℓ(q)) dq`, with `F(q) = (∫ f(q, x) dx) exp(−c ℓ(q))`.
     `F` is a.e. strongly measurable (Mathlib's `AEStronglyMeasurable.integral_prod_right'`).
     For `τ' > σ`, `‖F(q)‖ exp(τ' ℓ(q))` is at most
     `C exp(E(alphaQ q)) ∫ rectDecay`, by the bound of step 2 with `τ = τ' − c`.
     `RealConvergenceAnalysis.differentiableOn_integral_cexp_mul` then gives holomorphy. No
     Fubini theorem is needed.

## Relation to the literature

Jacquet (*Archimedean Rankin–Selberg integrals*, 2009, §5.2, pp. 33–35) proves convergence of
`Ψ_j(s; W, W')` for `Re s ≫ 0`. He treats only `j = n − n' − 1` and says the other cases are
similar. He writes the integral in the coordinates `g = ak` with the measure
`δ_n'(a)⁻¹ da dk dX` (his notation, p. 34; the formalization does not use `δ_n'`) and,
after a change of variables, moves `k` to the right of the block
matrix `[[a, 0, 0], [X, 1, 0], [0, 0, 1]]`. He majorizes the integrand by a power of the gauge
`ξ_h,n` of that matrix times polynomial factors and integrates over `k`. He then uses
`ξ_h,n(…) = ξ_i,n−1[[a, 0], [X, 1]]` up to a scalar and `ξ_i^n ≥ ξ_s`. Lemma 5.2 reduces the
problem to a product of an integral over `a`, which converges by Lemma 3.4, and an integral
over `X`.

The formalization keeps the product structure but differs in three points. It bounds the
Iwasawa coordinates of `rect(torus y · k, x)` directly (module `RealRectangularIwasawa`),
uniformly in the orthogonal matrix `k`, so no change of variables in `X` is needed. It
handles the quotient measure through the pushforward along the logarithmic toral Iwasawa
coordinate `alphaQ`, which the Weil formula and Haar uniqueness show to be `κ exp(L x) dx` for
a linear form `L` left unspecified (module `RealIwasawaMeasure`), so the abscissa `σ` is only
shown to exist. It obtains
holomorphy by differentiation under the integral sign.
