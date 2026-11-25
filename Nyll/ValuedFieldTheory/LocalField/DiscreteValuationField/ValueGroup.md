# Value subgroups of integer valuations and lcm divisibility

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file studies the set of values that an integer-valued valuation takes on a subgroup, viewed as a subgroup of `Multiplicative ℤ`, and compares it with the subgroups `dℤ` (`integerMultipleSubgroup d`). The aim is an lcm argument: if the values of a subgroup lie in `dℤ` and in `eℤ` and one of them is `n`, then `lcm(d, e)` divides `n`. The results are pure arithmetic of integers and of the library's `MultiplicativeIntegerValuation` on a group `G`.

## Results on integers

- `int_lcm_dvd_iff_dvd_and_dvd`: `lcm(d, e) ∣ n` iff `d ∣ n` and `e ∣ n`; `int_lcm_dvd_of_dvd_of_dvd` is the introduction form.
- `integerMultipleSubgroup_lcm_eq_inf`: `lcm(d, e)ℤ = dℤ ∩ eℤ`.
- `integerMultipleSubgroup_le_iff_dvd`: `bℤ ≤ aℤ` iff `a ∣ b`.
- `int_lcm_dvd_of_integerMultipleSubgroup_le_of_le`: if `nℤ ≤ dℤ` and `nℤ ≤ eℤ` then `lcm(d, e) ∣ n`.

## Value subgroups

- `MultiplicativeIntegerValuation.subgroupValueSubgroup V S`: the subgroup of values `V(x)` for `x ∈ S`; monotone in `S` (`subgroupValueSubgroup_mono`).
- `subgroupValueSubgroup_le_integerMultipleSubgroup_iff`: the values of `S` lie in `dℤ` iff `d` divides `V(x)` for all `x ∈ S`.
- `integerMultipleSubgroup_le_subgroupValueSubgroup_of_exists_mem_val`: if some `x ∈ S` has value `n`, then `nℤ` is contained in the values of `S`.
- `int_lcm_dvd_of_exists_mem_val_of_subgroupValueSubgroup_le` and its variant for `S ≤ T` with hypotheses on `T`: if `S` has an element of value `n` and the values (of `S` or of a larger `T`) lie in both `dℤ` and `eℤ`, then `lcm(d, e) ∣ n`.

The lcm is Mathlib's `Int.lcm`, a natural number cast back to `ℤ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValueGroup.lean`: the Lean file is the source byte for byte (SHA-256 `981c549af04ebcdad3ef073b975453c738d24428fa5c7b07dab92591856a4c91`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
