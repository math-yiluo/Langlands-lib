# Convergence of the logarithm series on the open unit ball

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.LogConvergence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field `K` with a valuation `v : Valuation K ℤᵐ⁰`, the file proves that the series log(1 + x) = Σ (−1)ⁿ xⁿ⁺¹/(n+1) converges for every x with v x < 1 (x = 0 included) when `K` is complete, identifies its sum with the evaluation of Mathlib's formal `PowerSeries.log`, and shows that above the threshold 1/(p − 1), or e/(p − 1) in the ramified form, log(1 + x) has the same valuation as x.

Throughout, `p` is a prime, `hnval` says v(n+1) = exp(−v_p(n+1)) for all n (the `_scaled_` versions use exp(−e·v_p(n+1))), and `hcomplete` says `K` is complete for `Valued.mk' v`.

## Convergence

- `tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one`: for v x < 1 the terms tend to 0 (no completeness needed).
- `summable_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one`, `hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_of_lt_one`, `tendsto_logOnePlusPartialSumField_ofWithZeroValuation_of_lt_one`: with completeness, the series converges to `logOnePlusSeriesFieldOfWithZeroValuation v x hnK`, and the partial sums converge to it; `_scaled_` versions likewise.
- `hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField`: with `[Algebra ℚ K]`, Σ coeffₙ(log) xⁿ has the same sum.
- `hasSum_formalLogOnePlusProductRightSide_monomialValue_pair`: for v x, v y < 1, the two-variable formal series log(1 + X) + log(1 + Y), evaluated monomial by monomial at (x, y), sums to log(1 + x) + log(1 + y); also termwise sums of two log series.
- Splitting lemmas: a summable log series equals x plus its tail, a summable exp series equals 1 plus its tail; and log(1 + 0) = 0.

## Valuation above the threshold

- `valuation_logSeriesTermField_lt_self_of_inv_sub_one_lt`: if x ≠ 0 has integer valuation above 1/(p − 1), every term of degree ≥ 2 has value strictly below v(x).
- `valuation_logHigherTailField_lt_self_of_inv_sub_one_lt`: hence v(log(1 + x) − x) < v(x), passing from partial sums to the limit because open balls are closed under limits.
- `valuation_logOnePlusSeriesField_eq_self_of_inv_sub_one_lt`: v(log(1 + x)) = v(x); so log(1 + x) ≠ 0 for x ≠ 0, and `logOnePlusSeriesField_eq_zero_iff_of_inv_sub_one_lt` gives log(1 + x) = 0 iff x = 0.
- The same four with `_scaled_` and threshold e/(p − 1).

## Watch for

- `hnval` is a hypothesis fixing the valuation of the integers; in the unscaled form it forces v(p) = exp(−1). It is not derived from a local-field structure here.
- The value is a `tsum`: the general lemmas that split off the first term take summability as a hypothesis; `logOnePlusSeriesField_eq_self_add_tsum_succ_ofWithZeroValuation_of_lt_one` obtains it for v x < 1 from the convergence result.
- The two-variable statement concerns only the side log(1 + X) + log(1 + Y) of the product formula; the formula log((1 + x)(1 + y)) = log(1 + x) + log(1 + y) is not proved in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/LogConvergence.lean`: the Lean file is the source byte for byte (SHA-256 `8434873f60baa43a1930eacca792c9b9a782cc5342e8859b666fb460f082a19d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
