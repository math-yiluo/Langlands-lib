# Archimedean indices of power subgroups

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.ArchimedeanPowerIndex`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file passes from the idele subgroup `h(S,T)` of local powers and local units (`idelePowerLocalUnitSubgroup`) to its image `C_K(S,T) = h(S,T)Kˣ/Kˣ` in the idele class group of a number field K, and computes, at each infinite place w, the index of the n-th powers in the local units `K_wˣ`.

## Definitions and results

- `ideleClassPowerLocalUnitSubgroup n S T`: the image of `h(S,T)` in `C_K`, with `mem_ideleClassPowerLocalUnitSubgroup_iff`; `IdeleClassPowerLocalUnitQuotient n S T` is the quotient `C_K / C_K(S,T)`, whose cardinality is the index `[C_K : C_K(S,T)]`.
- `realInfinitePlaceSignHom`: the sign of a unit at a real place, a surjection onto `SignTypeˣ` whose kernel is the positive subgroup `RayClass.infinitePositiveSubgroup w`; hence `realInfinitePositiveQuotientEquivSign` and `card_realInfinitePositiveQuotient` (the quotient has order 2).
- `nthPowerSubgroup_le_infinitePositiveSubgroup` and `nthPowerSubgroup_eq_infinitePositiveSubgroup`: if n is even or w is complex, the n-th powers in `K_wˣ` are exactly the positive units.
- `nthPowerSubgroup_eq_top_of_real_odd`: at a real place with n odd, every unit is an n-th power.
- `card_infinitePlace_nthPowerQuotient`: `#(K_wˣ / (K_wˣ)ⁿ)` is 2 when w is real and n even, and 1 otherwise.

## Proof

The reverse inclusions take n-th roots of positive units through the imported `exists_infinitePositiveSubgroup_nthRoot`; at a real place with n odd, a negative unit x equals `(-y)ⁿ` with `yⁿ = -x`.

## Points to watch

- "Positive" is the library's `RayClass.infinitePositiveSubgroup`: positivity under the real embedding at a real place, and the whole group at a complex place.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/IdeleClassPowerLocalUnitQuotient/ArchimedeanPowerIndex.lean`: the Lean file is the source byte for byte (SHA-256 `3a77676736259fde8fe540082c552d6e86098fe9b11d82ee4da6c94ab0f5b83f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
