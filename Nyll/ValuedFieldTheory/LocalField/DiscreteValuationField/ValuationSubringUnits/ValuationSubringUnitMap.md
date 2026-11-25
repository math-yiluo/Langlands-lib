# Units of the valuation ring inside the units of the field

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a complete discretely valued field `F : CompleteDVF K` of the library, the file defines the inclusion of unit groups `O_Kˣ → Kˣ`.

- `CompleteDVF.valuationSubringUnitsToFieldUnits F`: the group homomorphism from the units of the valuation ring `F.valuationSubring` to `Kˣ`, obtained from Mathlib's identification of `O_Kˣ` with the subgroup `unitGroup` of `Kˣ`.
- `coe_valuationSubringUnitsToFieldUnits_apply`: as an element of `K`, the image of a unit `a` is `a` itself.
- `valuationSubringUnitsToFieldUnits_mem_unitGroup`: the image lies in the unit group of the valuation ring, that is, has valuation `1`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/ValuationSubringUnitMap.lean`: the Lean file is the source byte for byte (SHA-256 `2723afda5f2670eca821415f855a035284002910f1a4103854505690900e8cd2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
