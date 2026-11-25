# Local units are norms at an unramified place

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension L/K with K a number field, this file shows that at a finite place v₀ of K where the library's chosen completion of L is unramified, every unit of the completed integers is a local norm.

- `adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup`: if `ChosenFinitePlaceIsUnramified v₀`, the units of Mathlib's `v₀.adicCompletionIntegers K` are contained in `chosenFinitePlaceLocalNormSubgroup v₀`, the norm subgroup of the chosen completion of L, carried into the units of the adic completion of K.

The proof moves a unit to the absolute-value completion of K through the units equivalence `finitePlaceCompletionUnitsContinuousMulEquiv`; it has norm at most 1, as does its inverse, so it is a unit of the valuation ring. It then applies the surjectivity of the norm on integer units in an unramified extension (`normIntegerUnits_surjective_unramified_of_isIntegralClosure`).

The unramifiedness hypothesis is the library's completed notion `ChosenFinitePlaceIsUnramified`, at the one chosen place above v₀.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Completion/UnramifiedComparison/LocalNorm.lean`: the Lean file is the source byte for byte (SHA-256 `4d2039309efd631627119c126fa0b07b9ad7872e384d366e281339cb41184f06`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
