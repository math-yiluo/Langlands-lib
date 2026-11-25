# exp ∘ log and log ∘ exp on the ramified convergence ball

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpComposition`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file evaluates the formal identities `exp(log(1 + X)) = 1 + X` and `log(1 + (exp X - 1)) = X` at elements `x` of a field `K`, complete for a valuation `v : Valuation K ℤᵐ⁰`, with `e/(p - 1) < val x`, where `val` is the additive valuation attached to `v`. To do so it proves a general theorem on evaluating a substitution of power series.

## Evaluation of substitutions

In a field with a `ℤᵐ⁰`-valued `Valued` structure, complete and nonarchimedean:

- `hasSum_powerSeries_pow_coeff_mul_pow`: if `∑ g_d x^d = y`, then `∑ (g^q)_d x^d = y^q` (by Cauchy products; this lemma only assumes a T3 uniform additive group structure making `K` a nonarchimedean ring).
- `valuation_powerSeries_pow_coeff_mul_pow_le` and `valuation_powerSeries_subst_sigmaTerm_le_outerTerm`: if `v(g_d x^d) ≤ v x` for all `d`, each term `f_q (g^q)_d x^d` has valuation at most `v(f_q x^q)`.
- `hasSum_powerSeries_subst_coeff_mul_pow`: let `g` have constant coefficient `0`, `∑ g_d x^d = y`, `∑ f_q x^q` summable, `∑ f_q y^q = z`, and `v(g_d x^d) ≤ v x` for all `d`. Then the evaluation at `x` of `PowerSeries.subst g f` (that is `f(g)`) has sum `z`. It combines `summable_powerSeries_subst_sigma_of_outer_summable`, `hasSum_powerSeries_subst_sigma` and the regrouping `hasSum_powerSeries_subst_coeff_mul_pow_of_sigma`.

## Scaled inputs and main results

The scaled results take a prime `p`, a natural number `e` and the threshold `e/(p - 1) < val x` for `x ≠ 0`; these alone give `v x < 1`. With `Algebra ℚ K` and the denominator hypotheses on `n + 1`, respectively on `n!`, the evaluated coefficients of `log(1 + X)` and of `exp X - 1` have valuation at most `v x`, without completeness. Adding completeness for `Valued.mk' v`, the formal exponential evaluates to `exp(x)`. The two main theorems use both sets of denominator hypotheses and completeness.

- `expSeries_logOnePlusSeries_eq_one_add_ofWithZeroValuation_scaled_of_threshold`: `exp(log(1 + x)) = 1 + x`.
- `logOnePlusSeries_expSeries_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold`: `log(1 + (exp(x) - 1)) = x`.

Both apply the substitution theorem to the formal identities `PowerSeries.exp_subst_log_eq_one_add_X` and `PowerSeries.log_subst_exp_sub_one_eq_X`. That the inner value again satisfies the threshold comes from the equalities `v(log(1 + x)) = v x` and `v(exp(x) - 1) = v x`, imported from other files.

## Points to watch

- The two main theorems carry four arithmetic hypotheses: `n + 1 ≠ 0` and `n! ≠ 0` in `K`, and `v(n + 1) = exp(-e · v_p(n + 1))` and `v(n!) = exp(-e · v_p(n!))`, with the same `e`. None is derived from `K`.
- The substitution theorem requires `f` to be summable at `x` itself, not only at `y`, and the coefficient bound `v(g_d x^d) ≤ v x`.
- The threshold is a strict inequality of real numbers involving `(ofWithZeroValuation v).val`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpComposition.lean`: the Lean file is the source byte for byte (SHA-256 `5560f217f22628165484e19eac0e121cd5e3f5ecd1f320e1be08bbfad71f7a83`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
