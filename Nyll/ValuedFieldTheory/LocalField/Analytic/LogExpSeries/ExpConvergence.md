# Convergence of the exponential series in a discretely valued field

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.ExpConvergence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a field with a valuation `v : Valuation K ℤᵐ⁰`, topologized by `Valued.mk' v`, and let `val = -log v` be the additive valuation `(ofWithZeroValuation v).val` on `Kˣ`. The file shows that `∑ xⁿ/n!` converges on a ball around `0`, that its value is multiplicative there, and that its partial sums are principal units. The terms, partial sums and the value (a `tsum`) are defined in another file: `expSeriesTerm` and `expSeriesOfWithZeroValuation` for units, `expSeriesTermField` and `expSeriesFieldOfWithZeroValuation` for field elements.

## Two radii

Every convergence result fixes a prime `p` and assumes `hnK` (`n! ≠ 0` in `K` for all `n`) and, for summation, `hcomplete` (completeness of `K` for `Valued.mk' v`).

- Normalized radius: `v x < exp(-1)`, that is `x = 0` or `val x ≥ 2`, with `hnval : v(n!) = exp(-v_p(n!))`. For units the hypothesis reads `1 < val x`.
- Sharp ramified radius: `e/(p - 1) < val x` for `x ≠ 0`, with `hnval : v(n!) = exp(-e · v_p(n!))` for a natural number `e`.

## Main results

For each radius, in turn: the valuations of `xⁿ/n!` tend to `+∞` (`ofWithZeroValuation_val_exp_term_tendsto_atTop_of_one_lt`, `ofWithZeroValuation_val_exp_term_scaled_tendsto_atTop_of_threshold`); the terms tend to `0`; they are summable, by the nonarchimedean criterion; the series has sum `expSeries…` and its partial sums converge to it. Field-element versions also cover `x = 0`.

- `expSeriesField_zero_ofWithZeroValuation`: `exp 0 = 1`, with no convergence hypothesis.
- `hasSum_formalExpPowerSeries_eval_expSeriesField`: on the normalized radius, with `Algebra ℚ K`, evaluating Mathlib's `PowerSeries.exp K` at `x` gives the same sum.
- `expSeriesField_add_eq_mul_ofWithZeroValuation_of_lt_exp_neg_one` and `…_scaled_of_threshold`: `exp(x + y) = exp(x) · exp(y)` on either radius, with `Algebra ℚ K`. The proof sums the Cauchy product with `Summable.mul_of_nonarchimedean` and compares it with the binomial expansion of the terms of `exp(x + y)`.
- `expSeriesField_neg_eq_inv_self_ofWithZeroValuation_of_lt_exp_neg_one` and companions: `exp(-x) · exp(x) = 1` and `exp(-x) = exp(x)⁻¹`.
- `expConvergenceAddSubgroupOfWithZeroValuation v`: the additive subgroup `{x | v x < exp(-1)}`.
- `valuation_expSeriesPartialSumField_sub_one_lt_one_of_lt_exp_neg_one`: every partial sum `s` through degree `N` satisfies `v(s - 1) < 1`; each positive-degree term has `v < 1`.

## Points to watch

- The valuation of `n!` is a hypothesis, not derived from `K`; `p` and `e` enter through `hnval` and, on the sharp radius, through the threshold. Comparing `hnval` at `n = p` and `n = p - 1` gives `v(p) = exp(-e)`.
- `hcomplete` is a proposition about the instance `Valued.mk' v`, and the conclusions about limits in `K`, summability and sums are stated under a local `let` of that instance.
- The inverse identities, the additive subgroup and the principal-unit statements are proved only on the normalized radius, not on the sharp ramified one.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/ExpConvergence.lean`: the Lean file is the source byte for byte (SHA-256 `90fc5042e2768b4636d98716aa987219ff85a8391ed53acdac018d9a65c3ff5b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
