# Integral induced units inside the local multiplicative block

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Inclusion`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields, `vK` a nontrivial nonarchimedean absolute value on `K`, and `w` an extension of `vK` to `L` (`AbsoluteValueExtension vK L`). The decomposition group of `w` (`absoluteValueDecompositionGroup K w.1`) acts on the unit group of the valuation ring of the localized completion `LocalizedCompletion vK w`. The file maps the module induced from these integer units into the library's local multiplicative induced block `LocalPlaceBlock vK hvK w`.

## Main declarations

- `inducedIntegerUnitsToLocalPlaceBlock`: a monoid hom from `CyclicCohomology.InducedModule` of the integer units to `LocalPlaceBlock vK hvK w`, given pointwise by the inclusion of integer units into field units. Elements of the induced module are functions `f` with `f (h g) = h • f g` for `h` in the decomposition group; the image satisfies the same rule because the inclusion commutes with the local Galois action (`integerUnitsToFieldUnits_galoisGroup_equivariant`, applied through `decompositionGroupEquivAlgebraicLocalizationAut`).
- `inducedIntegerUnitsToLocalPlaceBlock_injective`: this map is injective, since the inclusion of integer units into units is.

## Points to watch

- Both statements are made under a chain of `let`-bound structures (the algebra, valuation, valuative relation, valuation extension and integral-closure data, taken from `LocalInductionInternal`, and the action on integer units, which is `decompositionGroupLocalizedIntegerUnitsAction`). These are specific choices made by the library, not instances found by inference.
- `LocalPlaceBlock` and `InducedModule` are the library's own constructions.
- The injectivity theorem drops the number-field hypotheses on `K` and `L`.
- Both declarations take `K` and `L` in `Type`, the lowest universe.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/LocalInduction/Inclusion.lean`: the Lean file is the source byte for byte (SHA-256 `7bd67ed5020b9167aa7a39ffc98fe34955ed9aaf8e2e6da28f5c02047de93510`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
