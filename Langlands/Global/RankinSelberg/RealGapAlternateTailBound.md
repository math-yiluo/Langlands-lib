# Joint logarithmic and unipotent decay in the real alternate gap chart

This module is the real counterpart of the Library's `ComplexGapAlternateTailBound`, with the same
statement over `ℝ`. `rootPos` is the simple-root positivity function of
`RealConvergenceAnalysis`, `H` the real matrix height.

* `headDecay m x = (1 + ‖x‖)^{-m}` for `x ∈ ℝ^k`.
* `sum_abs_append`: the sum of absolute values is additive under `Fin.append`.

`RealGapAlternateTailBoundStatement` (proved by `realGapAlternateTailBound`): let `0 ≤ B` and
`A + 1 ≤ T`, `a : ℝˣ`, Schwartz column tests `Φ`, `Ψ` and `Ξ_j` (`j < q`), and `M`, `m : ℕ`. There are
`J`, `l` and `C ≥ 0` such that `unipotentDecay l` is integrable for `entryHaar (realSelfDualMeasure a) (q + 1)`
and, for `y ∈ ℝ^k`, outer coordinates `p` (tail logarithms `z`, first column `x`) and `Z ∈ N_{q+1}(ℝ)`,

`H(R)^M ‖Φ(firstRetainedColumn p)‖ ‖Ψ(lastRetainedInverseRow p)‖ ‖triangularFourier k q a R Ξ Z‖ ·
exp(A ∑|y_i| + B ∑|z_i| + T ∑ y_i − J · rootPos(append y (−z)))`
`≤ C · exp(−∑|y_i|) · exp(−∑|z_i|) · headDecay m x · unipotentDecay l Z`, where `R = retainedMatrix p`.

The order `m` of the first-column factor is arbitrary, so the statement asserts integrability only of
the unipotent factor. The factor `headDecay m` is integrable for an additive Haar measure on `ℝ^k`
when `m` exceeds the real dimension `k`; at `m = 0` it is the constant `1`.

The proof takes `l` and the bound for the alternate columns from `realGapAlternateColumnDecay`, bounds the
resulting power of `H(R)` by `height_retained_le`, absorbs the exponentials by the torus estimate
`RealGapTorusBound.exponent_le_first` (choosing `J` and the endpoint damping orders), and absorbs those
endpoint orders and the rectangular power by Schwartz seminorm estimates for `Φ` and `Ψ` through
`retained_endpoint_norms`.

This is an internal estimate supporting the absolute convergence of the larger-gap integrals in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.
