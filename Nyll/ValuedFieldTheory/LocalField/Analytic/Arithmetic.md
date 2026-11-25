# Arithmetic estimates for p-adic logarithm and exponential series, and lcm cancellation

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.Arithmetic`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file collects elementary arithmetic used elsewhere in the local-field development: estimates on `p`-adic valuations of `n` and of `n!` that control the convergence and the valuation of the logarithm and exponential series, and natural-number cancellation rules for `lcm` and `gcd` used in ramification-index computations (the tame Abhyankar formula). No field appears; all statements are about `ℕ`, `ℤ`, `ℚ` and `ℝ`, with `p` prime in the valuation estimates.

## Estimates for the logarithm series

- `pow_padicValNat_le_self`, `padicValNat_le_real_logb`: `p^(v_p(n)) ≤ n` for `n ≠ 0`, and `v_p(n) ≤ log_p n`.
- `tendsto_nat_mul_const_sub_logb_atTop` and variants with index `n + 1` and with a constant factor `C`: for `c > 0`, `n c − C log_p n → ∞`.
- `padicValNat_div_sub_one_le_inv_sub_one`: for `n > 1`, `v_p(n)/(n − 1) ≤ 1/(p − 1)`; `padicValNat_lt_sub_one_mul_of_inv_sub_one_lt` and `sub_padicValNat_pos_of_inv_sub_one_lt` give strict forms for a slope `c > 1/(p − 1)`.
- `log_higher_term_integer_valuation_gt`: for `n ≥ 2` and an integer `m > 1/(p − 1)`, `m < n m − v_p(n)`; the `_scaled` version replaces `v_p(n)` by `e v_p(n)` and the threshold by `e/(p − 1)`.

## Estimates for the exponential series

- `tendsto_nat_mul_const_sub_padicValNat_factorial_atTop`: for `c > 1`, `n c − v_p(n!) → ∞`.
- `padicValNat_factorial_digits`, `padicValNat_factorial_digits_sum`: Legendre's formula in digit form, `(p − 1) v_p(n!) = n − s_p(n)` with `s_p` the base-`p` digit sum.
- `sub_one_mul_padicValNat_factorial_le_sub_one`, `padicValNat_factorial_le_sub_one_div_sub_one_real`, `padicValNat_factorial_div_sub_one_le_inv_sub_one`: `(p − 1) v_p(n!) ≤ n − 1` for `n ≠ 0`, in several forms (the quotient form for `n > 1`).
- `tendsto_nat_mul_const_sub_const_mul_padicValNat_factorial_atTop`: for `C ≥ 0` and `c > C/(p − 1)`, `n c − C v_p(n!) → ∞`.
- `exp_higher_term_integer_valuation_gt`: for `n ≥ 2` and an integer `m ≥ 2`, `m < n m − v_p(n!)`; the `_scaled` version has threshold `e/(p − 1)`.

## lcm and gcd cancellation

`nat_lcm_div_right_eq_div_gcd` and `nat_lcm_div_left_eq_div_gcd` (`lcm(a, b)/b = a/gcd(a, b)` for `b > 0`), and consequences, also for `b > 0`: `lcm(a, b) ∣ b c` gives `a/gcd(a, b) ∣ c`; `b c ∣ lcm(a, b)` gives `c ∣ a/gcd(a, b)`; `b c = lcm(a, b)` gives `c = a/gcd(a, b)`; and left-handed forms. The `nat_abhyankar_*` lemmas specialise them to ramification indices: if `e' > 0` and `e' e_top = lcm(e, e')` then `e_top = e/gcd(e, e')`, which is `1` when also `e > 0` and `e ∣ e'`.

## Points to watch

- The non-scaled exponential comparison asks `m ≥ 2`, which is stronger than the threshold `m > 1/(p − 1)` when `p > 2`; the scaled version has the sharp threshold.
- The `nat_abhyankar_*` statements are arithmetic only: the equality `e' e_top = lcm(e, e')` is a hypothesis, not proved here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/Arithmetic.lean`: the Lean file is the source byte for byte (SHA-256 `6de1fef1ee185e91cac447191232cfee756819eec1d3e3bc853a55f9f5a683ce`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
