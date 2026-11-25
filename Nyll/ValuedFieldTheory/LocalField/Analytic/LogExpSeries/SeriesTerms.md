# Terms of the logarithm and exponential series over a ℤᵐ⁰-valued field

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.SeriesTerms`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file sets up the terms, partial sums and infinite sums of log(1 + x) = Σ (−1)ⁿ xⁿ⁺¹/(n+1) and exp(x) = Σ xⁿ/n! over a field `K` with a valuation `v : Valuation K ℤᵐ⁰`, relates them to Mathlib's formal power series `PowerSeries.log` and `PowerSeries.exp`, and proves that the logarithm series converges for x of positive valuation when `K` is complete.

## Definitions

- `logSeriesTerm`, `signedLogSeriesTerm`, `logOnePlusPartialSum` for a unit `x : Kˣ`, and their `Field` versions for any `x : K` (x = 0 allowed): xⁿ⁺¹/(n+1), (−1)ⁿ xⁿ⁺¹/(n+1) and the partial sums.
- `expSeriesTerm`, `expSeriesPartialSum` and their `Field` versions: xⁿ/n! and its partial sums.
- `logOnePlusSeriesOfWithZeroValuation`, `expSeriesOfWithZeroValuation` and `Field` versions: the `tsum` of the terms in the topology `Valued.mk' v`, hence 0 when the series is not summable.

Every definition carries a hypothesis `hnK` that the denominators n+1 (resp. n!) are nonzero in `K`.

## Results

- `powerSeries_log_coeff_mul_pow_eq_signedLogSeriesTermField`, `formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField` and partial-sum versions: with `[Algebra ℚ K]`, the terms are coefficients of `PowerSeries.log K` (shifted by one) and `PowerSeries.exp K` times powers of x.
- `expSeriesTermField_add_eq_sum_antidiagonal`: the n-th exponential term of x + y is the sum over i + j = n of products of terms of x and y; double-sum forms follow for partial sums.
- Bookkeeping between `v` and the integer valuation `ofWithZeroValuation v` (value −log v(x)): order reversal, positivity iff v x < 1, the ultrametric inequality, stability of open balls under sums and of the open unit ball under products, and `valuation_limit_lt_of_tendsto_of_eventually_lt` (a limit of a sequence eventually in an open ball of nonzero radius lies in it).
- `summable_signed_log_term_ofWithZeroValuation_of_pos`, `hasSum_signedLogSeriesTerm_logOnePlusSeries_ofWithZeroValuation_of_pos`, `tendsto_logOnePlusPartialSum_ofWithZeroValuation_of_pos`: for a prime `p`, a unit `x` of positive integer valuation and complete `K`, the signed series is summable with sum `logOnePlusSeriesOfWithZeroValuation v x hnK`, and the partial sums converge to it. `_scaled_` versions allow a ramification index `e`.

The valuation of xⁿ⁺¹/(n+1) tends to +∞ by a lemma of an imported file; Mathlib's criterion for complete nonarchimedean groups (terms tending to zero) gives summability.

## Watch for

- The convergence results assume `hnval`: v(n+1) = exp(−v_p(n+1)) for all n, or exp(−e·v_p(n+1)) in the `_scaled_` versions. It fixes how the integers are valued and is not derived here.
- Completeness is a hypothesis `hcomplete` about `Valued.mk' v`, not an instance.
- Convergence is proved for units `x : Kˣ` (the principal unit being 1 + x) and for the logarithm only. For the exponential the file has terms, formal identities and `ofWithZeroValuation_val_mk0_one_lt_of_lt_exp_neg_one` (v x < exp(−1) gives integer valuation above 1), but no convergence.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/SeriesTerms.lean`: the Lean file is the source byte for byte (SHA-256 `26ffa227db11a7fe4d3186f55c3dfa769a949c347acbc2359ed77c4bf1c99550`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
