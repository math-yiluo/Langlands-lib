# Integrals of functions constant on fibers, and `ℓ²` norms

## Statements

* `lintegral_comp_eq_mul_tsum`. Let `μ` be a measure on a measurable space `Q`, and let
  `p : Q → ι` be a map. Suppose every fiber `p ⁻¹' {i}` is measurable and has measure
  `c ≠ 0`. Then for every `v : ι → ℝ≥0∞`,
  `∫⁻ q, v (p q) ∂μ = c * ∑' i, v i`.
  The lemma assumes no measurability of `v` and no countability of `ι`.
* `lp_two_enorm_sq_eq_tsum`: for `F` in `ℓ²(X, ℂ)` (Mathlib's `lp (fun _ : X => ℂ) 2`),
  `‖F‖ₑ ^ 2 = ∑' α, ‖F α‖ₑ ^ 2` in `ℝ≥0∞`.
* `memℓp_two_of_tsum_enorm_ne_top`: a function `f : X → ℂ` with
  `∑' α, ‖f α‖ₑ ^ 2 ≠ ∞` satisfies `Memℓp f 2`.

## Provenance

These are internal helpers for the proof of the Remark of Renard IV.3.2
(`Langlands.Renard.CompactRepresentation.SingleCoefficientSquareIntegrabilityStatement`).
In that proof, `Q` is the quotient of the group by its center and `p` sends a point to its
coset modulo a compact open subgroup times the center. Every such coset then has the same
Haar measure. The lemma turns the integral of a function that is invariant under that
subgroup into a sum over the cosets. The facts are standard measure theory; the statements
and proofs are internal.

## Lean proof

* `lintegral_comp_eq_mul_tsum`. Write `1_i` for the indicator of `p ⁻¹' {i}` with constant
  value `v i`. Its integral is `v i * c` (`lintegral_indicator_const`).
  - `≤`: if `∑' i, v i = ∞` the right side is `∞`. Otherwise the support of `v` is countable
    (`Summable.countable_support_ennreal`). Pointwise, `v (p q)` is at most the countable
    sum of the `1_i` over the support. `lintegral_tsum` exchanges the integral and the
    countable sum, which gives `c * ∑'` over the support, and that is at most
    `c * ∑' i, v i`.
  - `≥`: write the sum as a supremum of finite sums (`ENNReal.tsum_eq_iSup_sum`). For a finite
    set `s`, `∑ i ∈ s, c * v i` is the integral of `∑ i ∈ s, 1_i`
    (`lintegral_finsetSum`), and this finite sum is at most `v (p q)` at each point,
    because at most one of the fibers contains `q`.
* `lp_two_enorm_sq_eq_tsum`: `lp.norm_rpow_eq_tsum` with exponent `2`, followed by
  `ENNReal.ofReal_tsum_of_nonneg`.
* `memℓp_two_of_tsum_enorm_ne_top`: `memℓp_gen_iff`. A finite sum in `ℝ≥0∞` of the coerced
  `‖f α‖₊ ^ 2` gives summability in `ℝ≥0` (`ENNReal.tsum_coe_ne_top_iff_summable`), and so
  summability in `ℝ`.

The file imports only Mathlib.
