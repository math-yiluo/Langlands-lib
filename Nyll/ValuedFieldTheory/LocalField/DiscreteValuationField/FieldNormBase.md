# Norm images of base units in a tower of fields

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNormBase`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file prepares, by pure field algebra, an Abhyankar-type norm-image argument. For a tower `K ⊆ L ⊆ M` it follows the units of `K` embedded in `L`, raises them to the power `[M : L]`, applies the norm from `L` to `K`, and shows that the results are norms from `M` down to `K`. No valuation appears.

## Main definitions and results

- `baseUnitsMap : Kˣ →* Lˣ`, induced by the algebra map, and its range `baseUnitsImageSubgroup`. They are compatible with towers (`baseUnitsMap_tower`, `baseUnitsImageSubgroup_map_le_tower`).
- `finrankPowerUnitsHom`: the endomorphism `x ↦ x^[M:L]` of `Lˣ`, where `[M:L]` is `Module.finrank L M`, which is zero when `M` is infinite-dimensional over `L`. `poweredBaseUnitsImageSubgroup` is the image of the embedded base units under it.
- `poweredBaseUnitsImageSubgroup_le_fieldNormSubgroup`: this subgroup lies in the norm subgroup `fieldNormSubgroup L M`, because the norm from `M` to `L` of `a ∈ L` is `a^[M:L]`.
- `normPoweredBaseUnitsImageSubgroup`: the image of the powered subgroup under `normUnits K L`, a subgroup of `Kˣ`.
- `normPoweredBaseUnitsImageSubgroup_le_fieldNormSubgroup_top`: it lies in `fieldNormSubgroup K M`. This uses transitivity of the norm, `normUnits K M z = normUnits K L (normUnits L M z)`.

## Points to watch

- The last result assumes `IsScalarTower K L M` and that `M` is a free `L`-module.
- The file does not compute the subgroup `normPoweredBaseUnitsImageSubgroup` (for instance as a group of `[M:K]`-th powers); it only places it inside the norm subgroup from `M`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/FieldNormBase.lean`: the Lean file is the source byte for byte (SHA-256 `a1c76ed19fbd17662806b445212bcd042a6a08178cf77eef12f571380ad784c6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
