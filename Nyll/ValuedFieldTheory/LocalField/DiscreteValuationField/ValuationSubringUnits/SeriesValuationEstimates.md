# Valuation estimates for the logarithm and exponential series

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.SeriesValuationEstimates`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a `ℤᵐ⁰`-valued valuation `v` on a field `K` and its additive integer valuation `val = ofWithZeroValuation v` on `Kˣ`, the file bounds `val` of the series terms `xⁿ/n!` and `xⁿ/n` from below and shows that these valuations tend to `+∞`. These are the convergence estimates for the exponential and the logarithm on units.

## Results

All statements take a natural number `p`, assumed prime (`Fact p.Prime`) except in the two factorial real lower bounds, and assume, as hypotheses, that the relevant integers are nonzero in `K` and that `v` gives them the expected `p`-adic value: `v(n!) = exp (-v_p(n!))`, or `exp (-e · v_p(n!))` in the `_scaled` versions, where `e` plays the role of a ramification index (and similarly for `n`).

- `ofWithZeroValuation_val_pow_div_natCast_factorial_pos_of_one_lt`: if `val x > 1` and `n ≠ 0`, then `val (xⁿ/n!) > 0`.
- `..._factorial_real_lower_bound` (and `_scaled`): if `c ≤ val x`, then `val (xⁿ/n!) ≥ n·c - v_p(n!)` (resp. `n·c - e·v_p(n!)`), in `ℝ`.
- `ofWithZeroValuation_val_pow_div_natCast_factorial_tendsto_atTop`: if `val x ≥ c > 1`, then `val (xⁿ/n!) → +∞`.
- `ofWithZeroValuation_val_pow_div_natCast_factorial_scaled_tendsto_atTop`: the same under `val x ≥ c > e/(p-1)`.
- `ofWithZeroValuation_val_pow_div_natCast_real_lower_bound` (and `_scaled`): if `c ≤ val x`, then `val (xⁿ/n) ≥ n·c - log_p n` (resp. `n·c - e·log_p n`).
- `ofWithZeroValuation_val_pow_succ_div_natCast_tendsto_atTop` (and `_scaled`): if `val x ≥ c > 0`, then `val (x^(n+1)/(n+1)) → +∞`.

## Proofs

Each bound rewrites `val` of the term exactly (from the integer-valuation file); the positivity statement then uses `v_p(n!) ≤ n`, the logarithm bounds use `v_p(n) ≤ log_p n`, and the factorial real bounds keep `v_p(n!)` as it is; the limits compare with real sequences shown to tend to `+∞` elsewhere in the library.

## Watch for

- The `p`-adic values of the denominators are hypotheses for every `n`, not consequences of an assumption on `K` or its residue characteristic.
- In the unscaled exponential statement the threshold is `c > 1`, not `1/(p-1)`; only the scaled version has threshold `e/(p-1)`.
- "Valuation" here is the additive integer valuation, so large means close to zero.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/SeriesValuationEstimates.lean`: the Lean file is the source byte for byte (SHA-256 `b9d4aad24401ce6e3715b05312e699b373bef4a5935ddbf7cebc21c37bdb1f3e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
