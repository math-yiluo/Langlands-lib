# Gauge estimates with constants uniform over a parameter set

This module sets up the estimates used to show that real unequal-rank Rankin–Selberg integrals are holomorphic in auxiliary parameters. It is internal supporting material for the continuation in the inducing exponents of Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.1. It is the real counterpart of the uniform simple-root bounds in the published complex family modules.

## Definitions

`HasLeftCharacter a W` says that a function `W` on `GL(n+1, ℝ)` transforms on the left under the upper unipotent group by the real Whittaker character of `a`: `W(u g) = ψ_a(u) W(g)` for every upper unipotent `u` and every `g`.

`HasUniformGauge S W` is the gauge estimate `RealEqualConvergence.HasGauge` for a family `W p` indexed by `p` in a set `S`, with constants that do not depend on `p`. Write `rootPos y` for the sum of the positive parts of the simple-root coordinates `y_i − y_(i+1)`. The predicate asks for one growth exponent `N` with the following property. For each decay order `M` there is one constant `C ≥ 0` such that

`‖W p (torus y · k)‖ ≤ C · exp(−M · rootPos y + N · Σ_j |y_j|)`

for every `p ∈ S`, every logarithmic torus coordinate `y` and every orthogonal `k`.

## Results

- `HasLeftCharacter.norm_eq`: the character has absolute value one, so `‖W(u g)‖ = ‖W g‖`.
- `HasUniformGauge.mono`: the predicate passes to subsets.
- `hasUniformGauge_const`: a constant family with a gauge has a uniform gauge.
- `HasUniformGauge.dual`: the gauge survives the Weyl inverse transpose `W ↦ W̃`. On a toral representative this transpose reverses and negates the logarithms and replaces the orthogonal factor by another orthogonal matrix. This preserves both `rootPos` and `Σ |y_j|`.
- `HasUniformGauge.translate`: the gauge survives right translation by a fixed orthogonal matrix, which is absorbed into the orthogonal factor.
- `hasUniformGauge_of_derivativeGrowth`: suppose that for every `p ∈ S` all iterated right derivatives of `W p` lie in the published regular class, and that for each derivative word they are bounded by `C · height(g)^N` with `N` and `C` independent of `p`. Then the family has a uniform gauge, with growth exponent `2N`. The proof is the published family gauge theorem `RealWhittakerGauge.gauge_bound_of_derivative_growth_family`, applied to the family indexed by the subtype `S`.
- `exists_uniform_derivativeGrowth`: suppose the family has locally uniform derivative growth on `Ω` (the published `RealGodement.HasLocallyUniformDerivativeGrowth`, with parameters in `ℂ^m`). Then on every compact `K ⊆ Ω` the bounds hold with one exponent and, for each derivative word, one constant. The proof covers `K` by finitely many of the given balls. It takes the largest exponent and the sum of the constants, and uses `height ≥ 1`.
- `HasUniformGauge.pad`: uniform form of `RealUnequalConvergence.pad_gauge`. For `t < r`, the gauge of a family on `GL(r+1, ℝ)` gives a bound on the padded points `diag(torus y · k, 1)`, `y ∈ ℝ^(t+1)`. The bound has an extra decay factor `exp(−M · max(y_last, 0))`. The padded torus has zero trailing coordinates, and its positive simple-root sum is the smaller one plus the positive part of the last smaller coordinate.
- `HasUniformGauge.any`: uniform form of `RealUnequalDualConvergence.gauge_any`. If each `V p` has left-invariant absolute value under the upper unipotent group, the toral bound holds at every `g` with `y` replaced by the Iwasawa logarithms `alpha g`.
- `HasUniformGauge.rect`: uniform form of `RealUnequalDualConvergence.rect_bound`. For `t < r` and families with left-invariant absolute value, the gauge evaluated at the rectangular points `rectangularPoint h (torus y · k) x` is bounded by

  `C · exp(−M · (Σ_j max(y_j, 0) + (t+1) log(1 + ‖x‖²)/2) + N · (Σ_j |y_j| + ((t+1) + (r−t−1)) log(1 + ‖x‖²)))`,

  where `‖x‖²` is the sum of squares of the entries of `x`. This comes from the published Iwasawa estimates for rectangular points (`decay_le`, `sum_abs_le`), applied with the decay order `((t+1) + 2(t+1)(r−t−1)) M`.
