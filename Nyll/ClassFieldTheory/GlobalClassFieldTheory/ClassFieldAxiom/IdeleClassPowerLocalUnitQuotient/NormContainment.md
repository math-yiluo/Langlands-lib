# Local-power ideles are norms

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.NormContainment`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a Galois extension of number fields whose Galois group is identified, through `eG`, with `(ℤ/n)^r`, and let S, T be finite sets of finite places of K. The file shows that the idele subgroup `h(S,T)` of local n-th powers and local units (`idelePowerLocalUnitSubgroup`) consists of norms, and passes to idele classes.

- `idelePowerLocalUnitSubgroup_le_relativeIdeleNorm_range`: `h(S,T) ⊆ N_{L/K}(I_L)`, provided n is even or K has no real place, every place of T splits completely in L, and every finite place outside `S ∪ T` is unramified in L (`ChosenFinitePlaceIsUnramified`).
- `ideleClassPowerLocalUnitSubgroup_le_ideleClassNorm_range`: hence `C_K(S,T) ⊆ N_{L/K}(C_L)`.

The proof checks the imported componentwise criterion for idele norms: at an infinite place an n-th power is positive, hence a local norm; at finite places it uses `idelePowerLocalUnitSubgroup_le_allFinitePlaceLocalNormCondition`.

## Points to watch

- Splitting and unramifiedness are the library's predicates on a chosen place above v.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/IdeleClassPowerLocalUnitQuotient/NormContainment.lean`: the Lean file is the source byte for byte (SHA-256 `98c0b70eb93b21845e8b3d0d7e2fd492f7e984924803afd99155ddd80d851815`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
