# Uniformizers and units for the induced integer valuation

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuationUniformizer`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a `ℤᵐ⁰`-valued valuation `v` on a field `K`, the file relates the integer valuation `ofWithZeroValuation v` on `Kˣ` to uniformizers and to the unit group of the valuation ring.

- `ofWithZeroValuation_isUniformizer_of_valuation_eq_exp_neg`: if `v π = exp (-1)`, then `π` is a uniformizer for the integer valuation; `ofWithZeroValuation_hasUniformizer_of_exists_valuation_eq_exp_neg` turns existence of such a `π` into `HasUniformizer`.
- `exists_unit_valuation_eq_exp_neg_of_surjective`, `ofWithZeroValuation_hasUniformizer_of_surjective`: when `v` is surjective, such a unit exists, so a uniformizer exists.
- `ofWithZeroValuation_val_surjective_of_surjective`: if `v` is surjective, the integer valuation `Kˣ → ℤ` is surjective.
- `ofWithZeroValuation_zeroSubgroup_eq_unitGroup`: the kernel of the integer valuation is the unit group of the valuation ring of `v`.
- `baseUnitsMap_zeroSubgroup_ofWithZeroValuation`: for a field extension `L/K`, both fields in the same universe, with `ℤᵐ⁰`-valued valuations such that `vL` extends `vK` (`HasExtension`), units of `K` of valuation zero map to units of `L` of valuation zero.

The uniformizer notion is that of the library's `MultiplicativeIntegerValuation` structure.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/IntegerValuationUniformizer.lean`: the Lean file is the source byte for byte (SHA-256 `549cf864097d9d4476051d7d7ab42c6893dddf68e7ee4861c7da427e351a431f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
