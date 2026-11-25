# Additivity of the logarithm series on principal units

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpAdditivity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a field complete for a valuation `v : Valuation K ℤᵐ⁰`, with `v(n) = exp(-e · v_p(n))` on positive integers. The file evaluates the formal identity `log((1 + X)(1 + Y)) = log(1 + X) + log(1 + Y)` at points of the open unit ball and deduces that the logarithm series is a homomorphism on the first principal units. The field value `logOnePlusSeriesFieldOfWithZeroValuation v x hnK` of `log(1 + x)` and the principal-unit logarithm are defined in other files.

## Hypotheses

The results take `Algebra ℚ K`, a prime `p`, a natural number `e`, `hnK` (`n + 1 ≠ 0` in `K`), `hnval : v(n + 1) = exp(-e · v_p(n + 1))`, and `hcomplete` (completeness for `Valued.mk' v`); the point conditions are `v x < 1`, `v y < 1`.

## Main results

- `hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled`: for `v x < 1`, `∑ coeffₙ(PowerSeries.log K) · xⁿ` has sum `log(1 + x)`.
- The monomial expansions at `(x, y)` of `log(1 + X)`, `log(1 + Y)` and of their sum `formalLogOnePlusProductRightSide K` have sums `log(1 + x)`, `log(1 + y)` and `log(1 + x) + log(1 + y)`.
- `summable_formalLogOnePlusProductArgument_logDegree_monomialValue_pair_ofWithZeroValuation_scaled`: the doubly indexed family `(q, d) ↦ coeff_q(log) · coeff_d((X + Y + XY)^q) · x^(d 0) · y^(d 1)` is summable.
- Summing first over `d` gives `log(1 + x + y + xy)`; regrouping by `d` gives the monomial expansion of `log` substituted at `X + Y + XY`, with the same sum.
- `logOnePlusSeriesField_mul_argument_eq_add_ofWithZeroValuation_scaled`: `log(1 + (x + y + xy)) = log(1 + x) + log(1 + y)`.
- `principalUnitLogSeries_mul_eq_add_ofWithZeroValuation_scaled`: `log(uw) = log u + log w` for `u, w` in the first principal unit group `higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1`.
- `principalUnitLogSeriesHomOfWithZeroValuationScaled`: the logarithm as a monoid homomorphism from the first principal units to `Multiplicative K`.

Helper lemmas give `v(m) ≤ 1` for natural numbers `m` and bound each family term by the larger of `v(coeff_q(log) · x^q)` and `v(coeff_q(log) · y^q)`.

## Proof

Summability uses the nonarchimedean criterion: a term with `q ≥ N` is bounded by the one-variable terms, which tend to `0`, and for `q < N` only finitely many `d` occur. The sums are then rearranged by `HasSum.sigma_of_hasSum` and `HasSum.sigma`, and the two sides are compared with `formalLogOnePlusProductFormula_hasSum_monomialValue_eq`.

## Points to watch

- `hnK` and `hnval` are hypotheses on `K`; the file does not derive them, and `p`, `e` enter only through them.
- Additivity is proved here and is not carried as a hypothesis; the homomorphism is built from it.
- The principal-unit results need both the instance `IsCompleteDiscrete v` and the hypothesis `hcomplete`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpAdditivity.lean`: the Lean file is the source byte for byte (SHA-256 `87eed1a573133b9bdf52128a6ff43da98f2d3698091d195f1e152c67aab742fd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
