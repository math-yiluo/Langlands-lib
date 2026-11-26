# Interior derivative bounds for a local elliptic equation

This module proves an interior estimate for one scalar linear equation `D u = 0` on an open set
`S` of `EuclideanSpace ℝ (Fin d)`. Here `D` is a `CoordinateScalarOperator` of order `r` with
`C^∞` complex coefficients on `S`, written in the standard coordinate basis, and its principal
symbol `D.principalSymbol x₀ ξ` does not vanish for any nonzero real covector `ξ` at one point
`x₀ ∈ S`.

## Main results

For positive order, `exists_localElliptic_interior_derivative_l2_bounds` gives a radius `R > 0` with `closedBall x₀ R ⊆ S` and finite constants `C m : ℝ≥0∞`. For every smooth solution `u` of `D u = 0` on `S` and every derivative order `m`,

`‖iteratedFDeriv ℝ m u x₀‖ₑ ≤ C m * eLpNorm u 2 (volume.restrict (closedBall x₀ R))`.

`exists_localElliptic_interior_derivative_bounds` gives the corresponding sup-norm form in every order. If `M` bounds `‖u‖` on the closed ball, the derivative of order `m` at `x₀` is bounded by a real constant times `M`. The constants and ball are independent of the solution. This is an interior regularity estimate for smooth elliptic equations, in the setting of Morrey–Nirenberg (1957), with weighted $L^2$ estimates and the Library's interpolation and pointwise Sobolev bounds.

## Auxiliary results

The module reuses four public Library lemmas instead of reproving them:
`derivWordNorm_le_opNorm_times_card` and `eLpNorm_half_ball_le_weightedDerivative` from
`Langlands.Analysis.LocalEllipticSystemPointwise`, and `absorbs_half` and
`weightedSeminorm_lt_top` from `Langlands.Analysis.LocalEllipticSystemBounds`. Their Markdown
states them.

- `ballWeightedSeminorm_lt_top_of_continuousOn_closedBall`: a function continuous on the closed
  ball has finite weighted seminorms `ballWeightedSeminorm`. This is `weightedSeminorm_lt_top`
  under the name used in this module.

It proves the following new results.
- `cutoffLeibnizConst d r` (a `def`, internal bookkeeping constant): the sum over `i ≤ r` of
  `d ^ r * (r choose i) * ballCutoffConst i`. `cutoffLeibnizConst_ne_top` says it is finite.
- `eLpNorm_derivWordNorm_ballCutoff_smul_le`: the Leibniz rule for the product of `u` with the
  Library cutoff `ballCutoff x₀ ρ σ`. The `L²` norm of the `k`-th ordered derivative tensor of
  the product is at most the sum over `i ≤ k` of
  `d ^ k * (k choose i) * ballCutoffConst i / (σ - ρ) ^ i` times the `L²` norm of
  `derivWordNorm (k - i) u` on `ball x₀ σ`.
- `eLpNorm_ballCutoff_smul_le` bounds the $L^2$ norm of the cutoff product by `volume (closedBall x₀ R) ^ (1/2) * M` under a sup bound `M`. `eLpNorm_ballCutoff_smul_le_restrict` bounds the same norm by the $L^2$ norm on the enclosing closed ball, since the cutoff takes values in `[0, 1]` and vanishes outside that ball.
- `ballWeightedSeminorm_le_interpolation` is the sup-norm form of the weighted interpolation estimate. Its proof uses a formulation with an arbitrary common bound for the cutoff products. A cutoff between radii `ρ` and `σ = (ρ + R) / 2` preserves the derivatives on `ball x₀ ρ`. Apply `orderedTensorL2Interpolation` at scale `ε * (σ - ρ)` to bound the lower-order derivative by the top derivative and the norm of the cutoff product. The Leibniz estimate bounds the top derivative by weighted seminorms on the original ball. The factors match because `R - ρ = 2 * (σ - ρ)`.

## Proof

For positive order, `coordinateScalarLocalEllipticity` extends ellipticity at `x₀` to a neighbourhood. Apply `exists_localEllipticSystem_weighted_bounds` on the intersection with `S` to the system indexed by `Unit` with zero coupling. It gives a closed ball and controls every weighted derivative seminorm by a constant times the sum `B` of the seminorms of orders `< r`.

Apply the interpolation estimate with the restricted $L^2$ norm as the common cutoff bound. The top order seminorm is itself bounded by a constant times `B`, so the sum of the interpolation inequalities has the form `B ≤ B / 2 + c * eLpNorm u 2 (volume.restrict (closedBall x₀ R))` after choosing `ε` small. The seminorms in `B` are finite by smoothness on a neighbourhood of the closed ball. Absorption bounds all weighted seminorms by the $L^2$ norm of `u`. Restricting to the ball of half the radius removes the weights. The averaged Taylor estimate `measure_ball_rpow_mul_enorm_iteratedFDeriv_le` then bounds each derivative at the centre by finitely many of these $L^2$ derivative bounds. Dividing by the positive square root of the volume gives the stated estimate. The sup-norm bound in positive order follows by bounding the restricted $L^2$ norm by the square root of the volume times `M`.

In order zero and positive dimension ellipticity makes the order-zero coefficient nonzero near `x₀`, so any solution vanishes there. In dimension zero the value bound is immediate and all derivatives of positive order vanish. `exists_localElliptic_interior_derivative_bounds_zero` implements these two cases.

The weighted seminorms and the localized estimate follow the scalar homogeneous case of Morrey–Nirenberg, *On the analyticity of the solutions of linear elliptic systems of partial differential equations* (1957), §5, pp. 287–290. The initial elliptic estimate is in Lemmas 5.1–5.3 and the averaged Taylor step is the pointwise estimate of the kind used in §2, Lemma 2.2. The absorption here uses the Library's ordered tensor interpolation and the coefficients only need smoothness. The retained original is `provided-17e51270c6d50eab8ff7b4142058b4ec69474b21e75225ec9952a95784e8229f`, SHA-256 `61c74249e27625fd25cb0a33d3c77d90ab6b5306fc9bccddc7a6d5314229f915`.
