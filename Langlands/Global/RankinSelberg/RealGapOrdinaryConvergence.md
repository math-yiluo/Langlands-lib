# Joint absolute convergence in the ordinary real gap chart

This module is the real counterpart of the Library's `ComplexGapOrdinaryConvergence`. Notation as in
`RealGapOrdinaryMajorant`; `t < r`, `δ(g) = |det g|`.

* `ordinaryGapProductMeasure r t D ν νY μ₁ μ₂ κ` is the product of the compatible quotient measure
  `D.measure` on `N_{t+1}\GL_{t+1}(ℝ)`, the rectangular measure `rectangularMeasure νY` on the lower
  `(r−t) × (t+1)` rectangle, and `((μ₁ × μ₂) × rectangularMeasure ν) × κ` on the right-tail coordinates.
* `firstTorusDecay A x = exp(−(A + 1) ∑_i |alphaQ x i|)` on the quotient.
  `integrable_firstTorusDecay`: if the logarithmic Iwasawa marginal of `D.measure` has the density
  `c · exp(L y)` for a continuous linear functional `L`, then `firstTorusDecay ‖L‖` is integrable for
  `D.measure`. Indeed `L y ≤ ‖L‖ ∑|y_i|`, and `exp(−∑|y_i|)` is Lebesgue integrable.

`RealGapOrdinaryConvergenceStatement` (proved by `realGapOrdinaryConvergence`): let `t < r`, let
`W : GL_{r+1}(ℝ) → ℂ` and `V : GL_{t+1}(ℝ) → ℂ` satisfy `HasGaugeBound`, let `D` be a real quotient
measure datum of rank `t`, `ν`, `νY` additive Haar measures on `ℝ`, `μ₁`, `μ₂` Haar measures on
`GL_{t+1}(ℝ)` and `GL_{r−t}(ℝ)`, and `κ` a Haar measure on the orthogonal group `O(r+1)`. There are
`σ` and `τ` such that for all `u ≥ σ`, `s ≥ τ`, all `b`, all Schwartz tests `Φ`, `Ξ`, `Ψ` and `C₀ ≥ 0`, every
function `F` that is a.e. strongly measurable for `ordinaryGapProductMeasure r t D ν νY μ₁ μ₂ κ` and
satisfies

`‖F (x, Y, (((z, w), X), v))‖ ≤ C₀ · ordinaryGapNorm h Φ Ξ Ψ W V u s b x.out z w X Y v`

at every point is integrable for that product measure.

The proof takes `c` and `L` from `RealIwasawa.exists_lintegral_alphaQ` and applies
`realGapOrdinaryMajorant` with the rate `A = ‖L‖`. It chooses the decay order `p` for the second
square factor by `RealGapLeadingSchwartz.exists_integrable_weightedMatrixTail` with no height power and
determinant exponent `r − t`. It chooses the rectangle orders above the real dimensions of the
rectangles, so that `(1 + ‖X‖)^{−i}` is integrable. The compact factor has finite mass. The product
of these integrable majorants dominates `‖F‖`, the representative `x.out` having
`alpha x.out = alphaQ x`. This gives the absolute convergence of the ordinary split integrals in
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.
