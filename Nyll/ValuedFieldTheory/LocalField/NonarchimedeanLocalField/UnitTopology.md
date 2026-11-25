# The unit group of 𝒪[K] as an open subgroup of Kˣ

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This short file describes the units of the valuation ring inside the multiplicative group of the field.

- `localBaseUnitSubgroup K`: the image of `𝒪[K]ˣ` in `Kˣ`, defined for any field with a valuative relation.
- `mem_localBaseUnitSubgroup_iff_valuation_eq_one`: a unit `x ∈ Kˣ` lies in this subgroup exactly when its valuation is `1`.
- `localBaseUnitSubgroup_isOpen`: for a nonarchimedean local field, the subgroup is open in `Kˣ` (with its usual unit-group topology).

The first statement builds the unit of `𝒪[K]` from `x` and `x⁻¹`, both of valuation at most one. Openness follows because the sphere `{x | v(x) = 1}` is open in `K` for the valuative topology and the inclusion `Kˣ → K` is continuous.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnitTopology.lean`: the Lean file is the source byte for byte (SHA-256 `c6744636b52913994c9d2353547515063a4e66b26b27de95c46def640761acb5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
