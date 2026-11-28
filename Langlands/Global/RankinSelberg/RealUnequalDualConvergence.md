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

`rectangular_toralExponent_le` gives the comparison of the two exponents in
this calculation before applying the exponential function. It also applies
when the coefficient has a uniform growth allowance in another slot.

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
  then `exp(E ∘ alphaQ)` is integrable. `integrable_exp_comp_alphaQ_of_le` allows any
  strictly positive coefficient on the sum of absolute values.

## The convergence criterion

`HasRectangularToralBound` bounds the scalar kernel on torus and orthogonal
coordinates by arbitrary decay in the positive toral coordinates, a fixed
exponential growth allowance in the absolute coordinates, and the fixed
integrable rectangular weight `rectDecay`. The lemma
`hasRectangularToralBound_of_log_bound` obtains this bound from simultaneous
toral and logarithmic rectangular decay by increasing the decay order.

`realRectangularToralConvergence` proves a common half-plane of absolute
convergence and holomorphy for continuous kernels with that bound and left
upper-unipotent invariance in the group coordinate. The orthogonal coordinate
descends to a continuous `kQ` on the quotient, and `torus(alphaQ q) · kQ(q)`
provides continuous representatives for evaluating the invariant kernel.
The logarithmic determinant is the sum of the toral coordinates. For a
large real determinant exponent, choose the decay order using `sum_coord_le`.
The resulting majorant is a product of the integrable toral weight from
`integrable_exp_comp_alphaQ` and the integrable rectangular weight.
The spectral integral on the product space is holomorphic by differentiation
under the integral sign. The real determinant shift translates the
convergence half-plane.

`exists_dual_convergence` applies the criterion to the continuous product
kernel `bkernel h V V' (g, x) = V(rect(g, x)) V'(g)`. It combines `rect_bound`
for `V` with the gauge of `V'` at decay order zero, then uses the determinant
shift `(r − t)/2`. Fubini's theorem identifies the product integral on the
convergence half-plane with the iterated integral `blockIntegral`.
The quotient measure is sigma finite by regularity and sigma compactness
of the Iwasawa section, and the rectangular measure is sigma finite.

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
