# The logarithm on the units of a p-adic field

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.ContinuousFieldUnitLog`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a field of characteristic zero with a complete discrete valuation `v : K → ℤᵐ⁰` and finite residue field, so a local field of mixed characteristic with residue characteristic `p`. The file proves that there is exactly one homomorphism `log : Kˣ → K` (to the additive group) which is continuous, kills `p`, and agrees on the first principal units `U¹` with the logarithm series `log(1 + x) = Σ (−1)^(n+1) xⁿ/n`.

## Main results

- `continuous_principalUnitLogSeriesHomOfWithZeroValuationScaled`: the logarithm series, as a homomorphism from `U¹` to the additive group of `K` (written `Multiplicative K`), is continuous. It is stated with explicit data: a `ℚ`-algebra structure on `K`, a prime `p`, a natural number `e` with `v(n + 1) = exp(−e · v_p(n + 1))` for all `n`, completeness of `K`, and `n + 1 ≠ 0` in `K`.
- `uniformizerValueExponent_residueCharacteristic_ne_zero`: `p`, as an element of `Kˣ`, has nonzero exponent with respect to a uniformizer, because `v(p) < 1`.
- `fieldUnitLogHomWithUniformizerValue_unique_of_killing`: on a complete discretely valued field of characteristic zero with finite residue field, a homomorphism `Kˣ → K` is determined by its restriction to `U¹` and the fact that it kills one unit `a` of nonzero uniformizer exponent; it then equals the library's extension `fieldUnitLogHomWithUniformizerValue` with the value on the uniformizer chosen to kill `a`.
- `continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_ofWithZeroValuation`: the inverse of the decomposition of `Kˣ` into residue roots of unity, first principal units and powers of a uniformizer is continuous for the topology defined directly by `v`.
- `existsUnique_continuous_log`: the existence and uniqueness statement above (the field-unit logarithm theorem of the library's local-field structure theory).

## Proofs

Continuity at `1`: near `1`, the additive valuation of `u − 1` exceeds `e/(p − 1)`, where the logarithm series preserves valuations. Existence: `Kˣ` is decomposed through a uniformizer `π`, the series logarithm is used on `U¹`, roots of unity go to `0`, and `log π` is chosen so that `log p = 0`; continuity follows from continuity of the inverse decomposition. Uniqueness: every such homomorphism kills roots of unity, so it is fixed by its values on `U¹` and on `π`, and the value on `π` is forced since `p` has nonzero uniformizer exponent.

## Points to watch

- The codomain is `Multiplicative K`; the condition `log p = 0` is written `L pUnit = 1`.
- The normalization `log p = 0` is built into the statement; uniqueness holds among homomorphisms satisfying all three conditions.
- The local field is presented by a valuation with values in `ℤᵐ⁰` (`WithZero (Multiplicative ℤ)`), with the topology of `Valued.mk' v`; `CharZero K` and a finite residue field are assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/ContinuousFieldUnitLog.lean`: the Lean file is the source byte for byte (SHA-256 `db9a41ccd087e71559abfade31ea200ad43f874181bc56aa3542fdfa235bfc81`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
