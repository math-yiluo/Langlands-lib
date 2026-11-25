# The integral induced block embeds into the local block

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInclusion`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields and `w₀` a finite place of `K`, with a chosen place of `L` above it and chosen local field `E`. The module induced from the decomposition group by the integer units `𝒪[E]ˣ` sits inside the local block built from the field units `Eˣ`.

- `chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock w₀`: the map from `ChosenFinitePlaceInducedIntegerUnits w₀` to `ChosenFinitePlaceLocalPlaceBlock w₀`, the underlying function of the imported `inducedIntegerUnitsToLocalPlaceBlock` for the `w₀`-adic absolute value.
- `chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_injective`: this map is injective, by the imported `inducedIntegerUnitsToLocalPlaceBlock_injective`.

The map is stated as a plain function between the two types; its multiplicativity is not recorded here. `K` and `L` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/ChosenPlaceIntegralBlockInclusion.lean`: the Lean file is the source byte for byte (SHA-256 `dbbea7db4ce5afa68d84b9d548b70ca320d74cebf3f198f742e76b3a62de750a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
