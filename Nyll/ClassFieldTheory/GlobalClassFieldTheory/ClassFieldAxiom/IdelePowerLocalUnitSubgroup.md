# Ideles that are local powers at chosen places and units outside S ∪ T

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitSubgroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K, an exponent `n ∈ ℕ+` and finite sets S, T of finite places, the file defines the subgroup `h(S,T)` of the idele group cut out by local power and unit conditions, its trace on Kˣ, and the subgroup of n-th powers of S-units, and compares the last two.

## Definitions and results

- `idelePowerLocalUnitSubgroup n S T`: ideles whose component is an n-th power in `K_wˣ` at every infinite place w, an n-th power in `K_vˣ` at every v ∈ S, and a unit of the local integers at every finite v ∉ S ∪ T. `mem_idelePowerLocalUnitSubgroup_iff` states this componentwise.
- `principalIdelePowerLocalUnitSubgroup n S T`: the units of K whose principal idele lies in `h(S,T)`.
- `sUnitNthPowersInField n U`: n-th powers of U-units, as a subgroup of Kˣ. `mem_sUnitNthPowersInField_iff`: x belongs to it exactly when x is a U-unit and an n-th power in Kˣ; the reverse direction uses the imported fact that an element whose power is a U-unit is itself a U-unit.
- `sUnitNthPowersInField_le_principalIdelePowerLocalUnitSubgroup`: n-th powers of `(S ∪ T)`-units satisfy all the local conditions.
- `principalIdelePowerLocalUnitSubgroup_le_sUnitGroup`: a unit of K satisfying the conditions is an `(S ∪ T)`-unit.

## Points to watch

- S, T and U consist of finite places only. Every infinite place carries the n-th power condition, and places of T outside S carry no condition at all.
- `SUnitGroup` is the library's subgroup of Kˣ (units at every finite place outside the given set), not a Mathlib notion.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/IdelePowerLocalUnitSubgroup.lean`: the Lean file is the source byte for byte (SHA-256 `73071b8d2d1ef7c4f5eb81aaf89eec23ff13317ed474c2fe0e623171d953d379`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
