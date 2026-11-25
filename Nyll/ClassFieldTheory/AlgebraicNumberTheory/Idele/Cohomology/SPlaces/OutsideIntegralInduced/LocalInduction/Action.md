# The decomposition-group action on local integer units

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Action`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields, `vK` a nontrivial nonarchimedean absolute value on `K`, and `w` an extension of `vK` to `L`, with decomposition group `D_w`. Write `E = LocalizedCompletion vK w` for the library's local field attached to `w`, a Galois extension of the completion `K_v`.

- `decompositionGroupLocalizedIntegerUnitsAction vK hvK hvKna w`: the action of `D_w` by group automorphisms on the integer units `𝒪[E]ˣ`. It is the action of `Gal(E / K_v)` on integer units (`galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure`), pulled back along the isomorphism `decompositionGroupEquivAlgebraicLocalizationAut` between `D_w` and `Gal(E / K_v)`.

The valued-field, valuation-extension and integral-closure structures on `K_v` and `E` that this action needs are supplied by the imported helpers in `LocalInductionInternal`. `K` and `L` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/LocalInduction/Action.lean`: the Lean file is the source byte for byte (SHA-256 `de8264f39d6ae5a7fbad47071e7b985d0a186fe6110de28bd4d2b7cfd65348d4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
