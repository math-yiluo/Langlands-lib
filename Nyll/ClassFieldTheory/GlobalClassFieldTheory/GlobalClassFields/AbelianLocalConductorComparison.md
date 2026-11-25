# Global and local conductor exponents at a finite place

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianLocalConductorComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

At a finite place `v` of a number field `K`, the library has two models of the completion: the completion `vK.Completion` for the `v`-adic absolute value `vK`, used by local class field theory, and the adic completion `K_v`, used by ideles and ray classes. The file shows that the canonical isomorphism between their unit groups matches the two principal-unit filtrations. For a finite abelian extension `L / K`, it deduces that `ideleClassNormLocalHigherUnitExponent v`, the least level at which the higher-unit group lies in the chosen local norm subgroup, is the local conductor exponent of the chosen localized extension.

## Main results

- `finitePlaceFieldPrincipalUnits_map_eq_localHigherUnitGroup`: the continuous isomorphism `vK.Completionˣ ≃ₜ* K_vˣ` maps the `n`-th principal units `fieldPrincipalUnits n` onto the ray-class higher-unit group `RayClass.localHigherUnitGroup v n`, for every `n`.
- `finitePlaceCompletion_valuationMap_eq_zero_of_mem_localHigherUnitGroup`: a higher unit, transported back, has valuation `0`.
- `localHigherUnits_le_chosenNormSubgroup_iff_fieldPrincipalUnits_le_normSubgroup` (`L / K` Galois): the higher-unit group of level `n` lies in the chosen local norm subgroup iff `U^(n)` lies in the norm group `N(Eˣ)`, where `E` is the localized completion of `L` at the chosen place above `v`.
- `ideleClassNormChosenFinitePlaceLocalConductorExponent v` (`L / K` abelian): the local conductor exponent of `E` over `vK.Completion`, defined with the local-field structure on the completion built inside the definition.
- `ideleClassNormLocalHigherUnitExponent_eq_localConductorExponent`: `ideleClassNormLocalHigherUnitExponent v` equals this local conductor exponent.

## Proof

Both exponents are the least `n` for which the corresponding unit group lies in the corresponding norm group; the containment criterion above transfers each defining property to the other side, giving the two inequalities.

## Points to watch

- All local data are taken at one chosen place of `L` above `v` (`chosenFinitePlaceExtension`).
- The file does not identify `ideleClassNormLocalHigherUnitExponent v` with the exponent at `v` of the minimal conductor of the norm group.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/AbelianLocalConductorComparison.lean`: the Lean file is the source byte for byte (SHA-256 `5d77e54b3061aee9b9c8e8f36ddf89497ec4a23c284ae9663022d420c087d715`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
