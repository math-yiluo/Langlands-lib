# A ramification dichotomy for quadratic extensions of local fields

Helper module for the proof of `Langlands.LocalUnitaryDivisionCommutativeStatement`.

## Integer logarithm

For a nonarchimedean local field `L`, `vlog L x = log (φ (valuation L x)) ∈ ℤ`, where
`φ = IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L`. Lemmas: `vlog_mul`, `vlog_le_iff`,
`vlog_eq_iff` (for nonzero arguments, `vlog` compares like the valuation) and `exists_vlog_eq`
(every integer is attained, by surjectivity of the valuation).

## Dichotomy

Setting: local fields `K`, `L`, `[Algebra K L]`; `σ : L →+* L` preserving the valuation (`hσ`),
fixing `K` (`hσK`), involutive (`hσσ`), with fixed elements exactly `K` (`hfix`); valuations
compatible (`hKL`).

* `exists_base_of_not_squares`: if some nonzero `c₀ ∈ K` has `valuation L c₀` not the square of
  a valuation of `L`, every nonzero `x ∈ L` has the valuation of an element of `K`. Indeed
  `vlog c₀` is odd; norms `y σ(y) ∈ K` have `vlog` equal to `2 vlog y`; so even values come from
  norms and odd values from `c₀` times norms.
* `exists_base_approx`: if `|u| = 1` and `|σ u - u| < 1`, then `|u - r| < 1` for some integral
  `r ∈ K`. With `T = u + σ u` and `N = u σ u` in `K`: if `|2| = 1`, take `r = T/2`; if `|2| < 1`,
  the residue field of `K` is finite of characteristic two, so squaring is bijective on it and
  some integral `r` has `|r² - N| < 1`; then `(u - r)² = (T - 2r) u + (r² - N)` has absolute value
  `< 1`.
* `exists_close_base`: under the conclusion of `exists_base_of_not_squares`, every `y` with
  `σ y ≠ y` satisfies `|y - k| ≤ |σ y - y|` for some `k ∈ K`. Induction on
  `vlog y - vlog (σ y - y)`: if `|y| > |σ y - y|`, write `y = c u` with `c ∈ K`, `|u| = 1`; then
  `|σ u - u| < 1`, `exists_base_approx` gives `r`, and `y - c r` has smaller absolute value and the
  same `σ y - y`.
* `exists_moved_of_not_squares`: under the same hypothesis on `c₀`, if `σ` moves some `θ₀`,
  there is `θ` with `|θ| ≤ 1` and `|σ θ - θ| = 1`: approximate `θ₀` by `K` as above and divide by
  an element of `K` with the valuation of `σ θ₀ - θ₀`.
