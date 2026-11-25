# First-order estimates for exp and log on a discretely valued field

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.InverseEstimates`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field `K` with a valuation `v : Valuation K ℤᵐ⁰`, complete for its topology, the file proves that on the convergence domain exp(x) − 1 is dominated by its linear term, deduces that log ∘ exp and exp ∘ log agree with the identity to first order, and translates this into congruences modulo powers of the maximal ideal.

## Exponential estimates

Two regimes run in parallel: the ball v x < exp(−1) with `hnval` saying v(n!) = exp(−v_p(n!)), and the `_scaled_` versions where v(n!) = exp(−e·v_p(n!)) and the integer valuation of x exceeds e/(p − 1).

- `expSeriesField_sub_one_eq_tsum_succ_ofWithZeroValuation_of_lt_exp_neg_one` and tail versions: exp(x) − 1 is the sum of the terms of degree ≥ 1.
- `valuation_expSeriesTermField_lt_self_of_lt_exp_neg_one`: for x ≠ 0, each term xⁿ/n! with n ≥ 2 has value strictly below v(x); the same then holds for the whole tail exp(x) − 1 − x (`valuation_expSeriesHigherTailField_lt_self_of_lt_exp_neg_one`).
- `valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_of_lt_exp_neg_one`: v(exp(x) − 1) = v(x); hence exp(x) = 1 iff x = 0, and v(exp x) = 1.

## Inverse estimates

- `valuation_log_exp_sub_self_lt_of_scaled_threshold`: above the threshold e/(p − 1), v(log(exp x) − x) < v(x).
- `valuation_exp_log_sub_self_lt_of_scaled_threshold`: likewise v(exp(log(1 + x)) − 1 − x) < v(x).
- `logOnePlusSeries_expSeries_sub_self_mem_maximalIdeal_pow_succ_of_mem_maximalIdeal_pow` and its `expSeries_logOnePlusSeries_…` companion: if a ∈ 𝔪ⁿ with e/(p − 1) < n, then an element b of the valuation subring whose field value is log(exp a) − a, respectively exp(log(1 + a)) − 1 − a (hypothesis `hb`), lies in 𝔪ⁿ⁺¹.

Each difference is split as (outer tail) + (inner tail), both of value below v(x).

## Other content

- `completeDVFOfWithZeroValuation`: the library's `CompleteDVF K` structure built from a `v` carrying an `IsCompleteDiscrete` instance.
- `mem_maximalIdeal_pow_ofWithZeroValuation_val_ge` and its converse: given a uniformizer π with v(π) = exp(−1), a ∈ 𝔪ⁿ iff its integer valuation is at least n.
- `hasSum_signedLogSeriesTermField_logOnePlusSeriesField_mul_argument`: for v x, v y < 1, the log series at x + y + xy converges to its `tsum`.
- `hasSum_formalLogOnePlusProductArgument_logDegree_monomialValue_pair_sigma_of_summable`: the family indexed by (log degree, monomial in x, y) sums to log(1 + x + y + xy).

## Watch for

- The inverse results are first-order congruences only; the comments state that the exact identities log(exp x) = x and exp(log(1 + x)) = 1 + x need the full composition argument, which is not here.
- The sigma-family result assumes `hsigma`, the summability of that family; it is the Fubini input and is not proved in this file.
- The hypotheses `hnval…` fix how the integers are valued, and `hcomplete` (completeness for `Valued.mk' v`) is a hypothesis rather than an instance. The maximal-ideal results also need v(π) = exp(−1).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/InverseEstimates.lean`: the Lean file is the source byte for byte (SHA-256 `696bd56ddc6937901990574aa5d9609036987dfeb2d7c49f59b84efbbbca29c9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
