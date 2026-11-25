# Absolute convergence of the real unfolded corank-one kernel

This module justifies the interchange of integrals in Jacquet, *Archimedean
Rankin–Selberg integrals* (2009), §8.3, p. 58, for the real kernel after
equation (8.3). It is a real port of the Library's
`ComplexAdjacentConvergence`. Write `H = GL_(r+1)(ℝ)`, `Q = N \ H`, and `m = r+1`.

`RealJacquet.RealAdjacentConvergenceStatement` takes the following data:

* quotient measure data `D`;
* a real character datum `c`, used through its determinant character `η`;
* a square-matrix Schwartz test `F`;
* a row function `f` that is continuous and of rapid decay;
* functions `U` and `V` on `H`.

The hypotheses on `U` and `V` are these:

* both are continuous;
* `U(u g) V(u g z) = U(g) V(g z)` for upper unipotent `u`;
* `U` satisfies the gauge estimate `HasGauge` of `RealEqualConvergence`;
* `V` is bounded by a constant times a power of `realMatrixHeight`.

It concludes that, for some real `σ` and every `s` with `Re s > σ`, the
kernel `realAdjacentUnfoldedKernel η F f U V s` is integrable on
`Q × H`. The measure is the product of `D.measure` and `D.groupHaar`. This
kernel is the hypothesis of `realLocalAdjacentUnfolding` and of the two
unfoldings in `RealAdjacentGodementUnfolding`.

## Proof

At a class `q` with toral coordinate `y = alphaQ q`, unipotent invariance
moves the representative to `x = torus y · k`. This uses the published
`eq_torus_mul_kpart`. On `x` the estimates are:

* the gauge bound gives `‖U x‖ ≤ C₁ exp(−M·rootPos y + N₁ Σ|y_j|)`, for every `M`;
* submultiplicativity of the height (`realMatrixHeight_mul_le`) and the
  torus height bound give
  `‖V(x z)‖ ≤ C₂ H₀ exp(2M₂ Σ|y_j|) height(z)^M₂`;
* rapid decay of `f` at the last row of `x` gives decay in the positive part
  of the last toral coordinate;
* `|det x|^(Re s) = exp(Re s · Σ y_j)`.

This bounds the kernel by a product. The `Q` factor is
`C exp(E(alphaQ q))`. It is integrable for large `Re s` by the toral
integrability criterion `integrable_of_toral_bound`. It uses the toral
coordinate formula `exists_lintegral_alphaQ` of the compatible quotient
measure. The `H` factor is `‖F z‖ height(z)^M₂ |det z|^(Re s + r/2 + Re e)`,
where `e` is the exponent of `c`. Its norm uses `|c(x)| = |x|^(Re e)`. It is
integrable as soon as its exponent is at least `m + 2M₂`. This follows from
`GodementJacquet.integrable_realMatrixWeightedNorm` (module `RealMatrixConvergence`).
Product integrability on `Q × H` follows from `Integrable.mul_prod`. The
kernel is continuous on `Q × H` because its lift to `H × H` is continuous and
the quotient map is open. So the product majorant gives integrability.

The threshold `σ` depends on the gauge exponent of `U`, the growth exponent of
`V`, the linear form of the toral measure and the exponent of `c`. No
statement about meromorphic continuation or a functional equation is made.
