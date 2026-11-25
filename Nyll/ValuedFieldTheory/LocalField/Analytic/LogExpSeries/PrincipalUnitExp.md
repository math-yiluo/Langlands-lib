# The exponential as a map into principal units

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.PrincipalUnitExp`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a complete discretely valued field `K` with valuation `v : Valuation K ℤᵐ⁰`, the file turns the value of the exponential series into an element of a principal unit group, proves that it converts sums into products, and packages it as an injective homomorphism. It also introduces the additive parameter u − 1 of a principal unit, used by the logarithm files.

Throughout, `p` is a prime, `hnval` prescribes v(n!), and `hcomplete` says `K` is complete for `Valued.mk' v`; the units live in `higherPrincipalUnitGroup` of `completeDVFOfWithZeroValuation v`.

## Exponential on the ball v x < exp(−1)

Here `hnval` says v(n!) = exp(−v_p(n!)).

- `principalUnitExpSeriesOfWithZeroValuation`: Exp(x) as an element of U¹.
- `principalUnitExpSeries_eq_one_iff_ofWithZeroValuation`: Exp(x) = 1 iff x = 0; also v(Exp(x) − 1) = v(x) and v(Exp x) = 1.
- `principalUnitExpSeries_add_eq_mul_ofWithZeroValuation`: with `[Algebra ℚ K]`, Exp(x + y) = Exp(x)·Exp(y); hence Exp(−x) = Exp(x)⁻¹.
- `principalUnitExpSeriesHomOfWithZeroValuation`: Exp as a homomorphism to U¹ from `Multiplicative (expConvergenceAddSubgroupOfWithZeroValuation v)`, an additive subgroup defined in an imported file whose elements satisfy v x < exp(−1). It is injective, and `principalUnitExpSeriesMulEquivRangeOfWithZeroValuation` is the isomorphism onto its range.

## Exponential on 𝔪ⁿ

- `principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled`: for n ≥ 1 with e/(p − 1) < n, a uniformizer π with v(π) = exp(−1), and v(m!) = exp(−e·v_p(m!)), Exp sends a ∈ 𝔪ⁿ to Uⁿ; its field value is the exponential series of a.
- `principalUnitExpSeries_maximalIdealPow_add_eq_mul_ofWithZeroValuationScaled`: with `[Algebra ℚ K]`, Exp(a + b) = Exp(a)·Exp(b) on 𝔪ⁿ.

Membership in Uⁿ comes from v(Exp(a) − 1) = v(a); multiplicativity is the field identity exp(x + y) = exp(x)·exp(y) of an imported file.

## The parameter u − 1

- `principalUnitSubOneOfWithZeroValuation v u`: the element u − 1 of `K`.
- It satisfies v(u − 1) < 1, is topologically nilpotent, and two such parameters form a valid evaluation point for two-variable power series (`principalUnitSubOne_pair_hasEval_ofWithZeroValuation`).
- `principalUnitSubOne_eq_zero_iff_ofWithZeroValuation`: u − 1 = 0 iff u = 1; `principalUnitSubOne_mul_ofWithZeroValuation`: uw − 1 = (u − 1) + (w − 1) + (u − 1)(w − 1).
- For u = Exp(x) with x ≠ 0, u − 1 is nonzero and has the integer valuation of x, so it keeps the threshold 1/(p − 1).

## Watch for

- The homomorphism on the ball is shown injective only; no surjectivity onto a principal unit subgroup is proved, hence the isomorphism with the range.
- In the unscaled results the ball v x < exp(−1) means integer valuation at least 2, and `hnval` forces v(p) = exp(−1). The `Scaled` results use the threshold e/(p − 1) instead.
- `hcomplete` is a hypothesis besides the instance `IsCompleteDiscrete v`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/PrincipalUnitExp.lean`: the Lean file is the source byte for byte (SHA-256 `806b530a890d16ef5f42b54612a140b79790a6c458c059b3dc872d5812e312fe`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
