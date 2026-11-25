# Continuity of exp and log between mⁿ and Uⁿ

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpContinuity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be complete for a discrete valuation `v : Valuation K ℤᵐ⁰` (instance `IsCompleteDiscrete v`), with valuation ring `O`, maximal ideal `m` and higher principal unit groups `Uⁿ` (`higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) n`). For `n ≥ 1` with `e/(p - 1) < n`, the exponential and logarithm series give maps `mⁿ → Uⁿ` and `Uⁿ → mⁿ`, defined in other files. This file proves that both are continuous and assembles a topological group isomorphism from them.

## Hypotheses

Throughout: `Algebra ℚ K`, a prime `p`, natural numbers `e` and `n` with `1 ≤ n` and `e/(p - 1) < n` in `ℚ`, an element `π` of `O` with `v π = exp(-1)`, and completeness of `K` for `Valued.mk' v`. The exponential side assumes `k! ≠ 0` and `v(k!) = exp(-e · v_p(k!))` for all `k`; the logarithm side assumes `k + 1 ≠ 0` and `v(k + 1) = exp(-e · v_p(k + 1))`.

## Main definitions and results

- `principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled`: the exponential as a monoid homomorphism `Multiplicative (mⁿ) →* Uⁿ`, built from its additivity; `principalUnitExpSeriesHomOfMaximalIdealPow_apply` unfolds it.
- `continuousAt_zero_principalUnitExpSeries_maximalIdealPow_fieldVal_ofWithZeroValuationScaled`: the value in `K` of `exp(a)` is continuous at `a = 0`, because `v(exp(a) - 1) = v(a)` once `a ∈ mⁿ` lies above the threshold.
- `continuous_principalUnitExpSeries_maximalIdealPow_fieldVal_ofWithZeroValuationScaled`: the same map is continuous everywhere, by `exp(b) = exp(a) · exp(b - a)`.
- `continuous_principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled`: the homomorphism is continuous into `Uⁿ`; the inverse component of the unit topology is handled as `exp(-a)`.
- `continuous_principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled`: the logarithm `Uⁿ → mⁿ` is continuous, as the restriction of the continuous logarithm on `U¹`.
- `principalUnitExpLogContinuousMulEquivOfExact_ofWithZeroValuationScaled`: an isomorphism of topological groups `Multiplicative (mⁿ) ≃ₜ* Uⁿ`.

## Points to watch

- The isomorphism takes two hypotheses, `hlog_exp` (`log(exp a) = a` for every `a ∈ mⁿ`) and `hexp_log` (`exp(log u) = u` for every `u ∈ Uⁿ`). They stand for the two composition identities of the exponential and the logarithm, which this file does not prove; only continuity is supplied here.
- Topologies: `K` carries the topology of `Valued.mk' v`, `mⁿ` the subspace topology inside `O`, and `Uⁿ` the topology induced from the units of `O`, which also tracks inverses.
- The threshold `e/(p - 1) < n` is a rational inequality; `p` and `e` enter only through it and the valuation formulas for `k!` and `k + 1`.
- `π` must have valuation exactly `exp(-1)`; it is turned into a uniformizer by `isUniformizer_of_valuation_eq_exp_neg_one`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpContinuity.lean`: the Lean file is the source byte for byte (SHA-256 `05c8d5e7bd6816396cb2fc2ec26020e5c11a971150453fa232bd7f88f12ad4db`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
