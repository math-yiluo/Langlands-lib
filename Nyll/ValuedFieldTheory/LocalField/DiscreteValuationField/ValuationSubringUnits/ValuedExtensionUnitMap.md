# Units and uniformizers under an extension of complete DVFs

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuedExtensionUnitMap`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For complete discretely valued fields `K` and `L` of the library (`base` and `target`), in the same universe, with `L` a `K`-algebra and the valuation of `L` extending that of `K` (`HasExtension`), the file compares valuation-ring units and computes the valuation of a base uniformizer in `L`.

- `baseUnitsMap_mem_target_unitGroup_of_mem_base_unitGroup` and `baseUnitGroup_map_le_target_unitGroup`: units of `K` of valuation one map to units of `L` of valuation one.
- `baseUnitsMap_valuationSubringUnitsToFieldUnits`: the inclusions `O_Kˣ → Kˣ` and `O_Lˣ → Lˣ` commute with the maps induced by `K → L`.
- `base_uniformizer_image_val_eq_ramificationIndex`: let `vL` be any integer valuation on `Lˣ` that vanishes on the units of `O_L` and gives a uniformizer `π` of `L` the value `1`. Then a uniformizer `ϖ` of `K` has `vL`-value the ramification index `e(L/K)` (the library's `ramificationIndex`).

The last result writes the image of `ϖ` as a unit times `π^e`, an earlier result of the library on ramification ideals, and evaluates `vL`. The vanishing on units and the normalization `vL(π) = 1` are hypotheses on `vL`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/ValuedExtensionUnitMap.lean`: the Lean file is the source byte for byte (SHA-256 `a3da8f857993f1fb67cd438003c959ee8317248f0531669d173c7d326810794a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
