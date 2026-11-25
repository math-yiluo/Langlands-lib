# Equivariance of the inclusion of the integral induced block

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInducedSmul`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields with group `G` and `w₀` a finite place of `K`. The module induced from the decomposition group of the chosen place above `w₀` by the integer units of the chosen local field embeds into the local block of field units (`chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock`).

- `chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_smul`: for every `τ ∈ G`, this inclusion commutes with the actions of `τ` on the induced module (`chosenFinitePlaceInducedIntegerUnitsAction`) and on the local block (`chosenFinitePlaceLocalPlaceBlockAction`).

The identity holds by definition (`rfl`): both actions are induced-module actions and the inclusion acts coordinatewise. `K` and `L` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/ChosenPlaceIntegralBlockInducedSmul.lean`: the Lean file is the source byte for byte (SHA-256 `b397264d91c117481044725c8c26482d8bf1708e771b2c2d29ae3768b1958ba2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
