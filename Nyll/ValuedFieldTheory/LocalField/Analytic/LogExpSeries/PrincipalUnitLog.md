# The logarithm on Uⁿ and conditional equivalences 𝔪ⁿ ≅ Uⁿ

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.PrincipalUnitLog`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a complete discretely valued field `K` with valuation `v : Valuation K ℤᵐ⁰`, the file defines the logarithm of a principal unit, shows that it maps Uⁿ into 𝔪ⁿ when n > e/(p − 1), proves that Log(Exp a) ≡ a modulo 𝔪ⁿ⁺¹ for a ∈ 𝔪ⁿ and Exp(Log u) ≡ u modulo Uⁿ⁺¹ for u ∈ Uⁿ, and packages the equivalence 𝔪ⁿ ≅ Uⁿ under the hypothesis that Log and Exp are inverse exactly.

## Definitions

- `principalUnitLogSeriesOfWithZeroValuation v u hnK`: for u ∈ U¹, the value of the log series at u − 1 (a `tsum`).
- `principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled`: Log as a map Uⁿ → 𝔪ⁿ. Hypotheses: n ≥ 1, e/(p − 1) < n, a uniformizer π with v(π) = exp(−1), v(m+1) = exp(−e·v_p(m+1)) for all m, and completeness of `Valued.mk' v`.

## Results

The `Scaled` results below take these hypotheses together with the factorial analogue v(m!) = exp(−e·v_p(m!)) used by Exp.

- `principalUnitLogSeries_expSeries_maximalIdealPowSuccQuot_eq_self_ofWithZeroValuationScaled`: Log(Exp a) and a have the same class in 𝔪ⁿ/𝔪ⁿ⁺¹ for a ∈ 𝔪ⁿ; equivalently Log(Exp a) − a ∈ 𝔪ⁿ⁺¹, i.e. Log(Exp a) = a in 𝒪/𝔪ⁿ⁺¹.
- `principalUnitExpSeries_logSeries_principalUnitSuccQuot_eq_self_ofWithZeroValuationScaled`: Exp(Log u) and u have the same class in Uⁿ/Uⁿ⁺¹ for u ∈ Uⁿ; also Exp(Log u) ≡ u modulo 𝔪ⁿ⁺¹.
- `maximalIdealPowSubtype_eq_of_idealQuotient_eq_ge` and `higherPrincipalUnitGroup_eq_of_idealQuotient_eq_ge`: two elements of 𝔪ⁿ, or of Uⁿ, are equal if their images in 𝒪/𝔪ʳ agree for every r ≥ n.
- `principalUnitLogSeries_expSeries_eq_self_of_idealQuotient_eq_ge_ofWithZeroValuationScaled` and its Exp ∘ Log companion: the composite is the identity if it is so in 𝒪/𝔪ʳ for every r ≥ n; the `_of_sub_mem_ge_` versions take membership of the difference in each 𝔪ʳ instead.
- `principalUnitExpLogEquivOfExact_ofWithZeroValuationScaled` (a bijection 𝔪ⁿ ≃ Uⁿ) and `principalUnitExpLogMulEquivOfExact_ofWithZeroValuationScaled` (an isomorphism from `Multiplicative 𝔪ⁿ`, needing `[Algebra ℚ K]`): Exp with inverse Log; multiplicativity comes from Exp(a + b) = Exp(a)·Exp(b) of an imported file. The `OfIdealQuotient_ge` and `OfSubMem_ge` variants feed in the reductions above.

The graded statements come from the first-order congruences log(exp a) − a ∈ 𝔪ⁿ⁺¹ and exp(log(1 + a)) − 1 − a ∈ 𝔪ⁿ⁺¹ of an imported file.

## Watch for

- Every equivalence takes as hypotheses the exact identities Log(Exp a) = a on 𝔪ⁿ and Exp(Log u) = u on Uⁿ (`hlog_exp`, `hexp_log`), or their versions at all levels r ≥ n (`hlog_exp_quot`, `hexp_log_quot`, `hlog_exp_mem`, `hexp_log_mem`). The file proves the identities only modulo 𝔪ⁿ⁺¹; its comments describe the remaining all-level estimates as still to be supplied.
- `principalUnitLogSeriesOfWithZeroValuation` is a `tsum` and carries no convergence hypothesis; its value is meaningful only where the series converges.
- The integers' valuations are prescribed by hypotheses, not derived; `hcomplete` is assumed besides the instance `IsCompleteDiscrete v`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/PrincipalUnitLog.lean`: the Lean file is the source byte for byte (SHA-256 `b1a20d15aa0e7b82fb4e0e6ad1937d95791ff5f4e883b97a3491116fdfc04424`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
