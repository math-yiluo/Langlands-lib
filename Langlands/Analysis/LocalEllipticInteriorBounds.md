# Interior derivative bounds by the sup norm for a local elliptic equation

This module proves an interior estimate for one scalar linear equation `D u = 0` on an open set
`S` of `EuclideanSpace ℝ (Fin d)`. Here `D` is a `CoordinateScalarOperator` of order `r` with
`C^∞` complex coefficients on `S`, written in the standard coordinate basis, and its principal
symbol `D.principalSymbol x₀ ξ` does not vanish for any nonzero real covector `ξ` at one point
`x₀ ∈ S`.

## Main result

`exists_localElliptic_interior_derivative_bounds` gives a radius `R > 0` with
`closedBall x₀ R ⊆ S` and constants `C m ≥ 0` (`m : ℕ`). For every smooth solution `u` of
`D u = 0` on `S` and every real `M` that bounds `‖u‖` on `closedBall x₀ R`,
`‖iteratedFDeriv ℝ m u x₀‖ ≤ C m * M`. The ball and the constants depend only on `D`, `S` and
`x₀`, not on `u`. The theorem holds for every order `r`, including `r = 0`.

This is a pointwise form of the interior regularity estimate for elliptic equations with `C^∞`
coefficients, Morrey–Nirenberg (1957), Theorem C. The proof here does not follow their argument.
It combines `L²` estimates already in the Library with an interpolation step that bounds the
lower derivatives by the sup norm.

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
- `eLpNorm_ballCutoff_smul_le`: the `L²` norm of the cutoff product is at most
  `volume (closedBall x₀ R) ^ (1/2) * M`.
- `ballWeightedSeminorm_le_interpolation`: scale-explicit interpolation. For `k ≤ r`, `0 < ε`
  and a smooth `u` on `ball x₀ R` bounded by `M` on the closed ball, the `k`-th weighted
  seminorm on `ball x₀ R` is at most
  `2 ^ k * ε ^ (r - k) * cutoffLeibnizConst d r * ∑_{j ≤ r} (weighted seminorm of order j)`
  plus `2 ^ k * ε⁻¹ ^ k * volume (closedBall x₀ R) ^ (1/2) * M`.
  - **Proof.** For each inner radius `ρ` of the weighted seminorm, set
    `σ = (ρ + R) / 2` and `δ = σ - ρ`. Multiply `u` by `ballCutoff x₀ ρ σ`. The product is
    smooth with compact support and agrees with `u` on `ball x₀ ρ`. The Library interpolation
    `orderedTensorL2Interpolation` at scale `ε * δ` bounds its `k`-th tensor by its `r`-th
    tensor and its `L²` norm. The two auxiliary bounds above then express both in terms of the
    weighted seminorms of `u` and of `M`. The powers of `δ` match the weights `(R - ρ) ^ k`
    because `R - ρ = 2 δ`.

## Proof of the main result

**Positive order** (`exists_localElliptic_interior_derivative_bounds_of_pos`).
1. `coordinateScalarLocalEllipticity` extends ellipticity at `x₀` to an open neighbourhood `U`.
2. `exists_localEllipticSystem_weighted_bounds`, applied with a one-element index type and the
   zero coupling matrix on `S ∩ U`, gives a ball `closedBall x₀ R ⊆ S`. On that ball, every
   weighted seminorm of a solution is at most `C m * B`, where `B` bounds the weighted
   seminorms of orders `< r`.
3. Take `B` to be the sum of the weighted seminorms of orders `< r`. It is finite by
   `ballWeightedSeminorm_lt_top_of_continuousOn_closedBall`.
4. The interpolation bound for each order `k < r`, with
   `ε = 1 / (2 (A + 1))` where `A = r * 2 ^ r * cutoffLeibnizConst d r * (1 + C r)`, gives
   `B ≤ (1/2) B + K₀' M` with `K₀' = r * 2 ^ r * ε⁻¹ ^ r * volume (closedBall x₀ R) ^ (1/2)`.
   The Library lemma `absorbs_half` (it needs `B ≠ ⊤`, step 3) gives `B ≤ K₀ M` with
   `K₀ = 2 K₀'`, so the `m`-th weighted seminorm is at most `C m * K₀ * M`.
5. The Library lemma `eLpNorm_half_ball_le_weightedDerivative` bounds the `L²` norm of
   `iteratedFDeriv ℝ m u` on `ball x₀ (R/2)` by `((R - R/2) ^ m)⁻¹` times the `m`-th weighted
   seminorm, hence by `L m * M` with `L m = ((R - R/2) ^ m)⁻¹ * C m * K₀`.
6. The Library averaged Taylor estimate `measure_ball_rpow_mul_enorm_iteratedFDeriv_le`, applied
   on `ball x₀ (R/2)` to the derivative of order `m` with Taylor order `n = finrank ℝ E`, gives
   `volume (ball x₀ (R/2)) ^ (1/2) * ‖iteratedFDeriv ℝ m u x₀‖` at most the sum over `j ≤ n` of
   `(R/2) ^ j / j!` times the `L²` norm of the derivative of order `j + m`, plus a remainder
   `(R/2) ^ (n + 1) / n!` times the `L²` norm of the derivative of order `m + n + 1`. Inserting
   the bounds of step 5 and dividing by the positive finite volume factor gives
   `‖iteratedFDeriv ℝ m u x₀‖ ≤ C' m * M`. The constant `C' m` is the real value of the
   resulting finite `ℝ≥0∞` constant and does not depend on `u` or `M`. It is the constant
   called `C m` in the theorem; in steps 2–5, `C m` denotes the system constants of step 2.

**Order zero** (`exists_localElliptic_interior_derivative_bounds_zero`). Choose any closed ball
in `S` around `x₀`.
- If `d = 0`, the space is a single point. Every derivative of positive order vanishes, and the
  value at `x₀` is bounded by `M`. So `C m = 1` for `m = 0` and `C m = 0` otherwise.
- If `d > 0`, `D u = c * u`, where `c` is the sum of the order-zero coefficients. Applied to the
  nonzero covector `EuclideanSpace.proj 0`, ellipticity says `c x₀ ≠ 0`. By continuity `c ≠ 0`
  near `x₀`, so every solution vanishes near `x₀`. All its derivatives at `x₀` are then `0`,
  and `C m = 0` works.

The wrapper `exists_localElliptic_interior_derivative_bounds` splits on `r = 0`.
