# Galois equivariance of the integral induced block

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlock`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields with group `G` and `w₀` a finite place of `K`. The integral unit subgroup of `(w₀.adicCompletion K ⊗[K] L)ˣ` is identified with the module induced from the decomposition group of the chosen place above `w₀` by the integer units `𝒪[E]ˣ` of the chosen local field.

- `relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits_smul`: this identification is equivariant for the whole group `G`.

The proof maps both sides into the local block of field units by the injective inclusion `chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock`. There it combines three imported facts: the inclusion is compatible with the field-unit equivalence `finitePlaceTensorUnitsEquivLocalPlaceBlock`, that equivalence is equivariant on integral elements, and the inclusion is equivariant. `K` and `L` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/ChosenPlaceIntegralBlock.lean`: the Lean file is the source byte for byte (SHA-256 `8a0925f5b95126cd65f09dd363b9e024ba28806b15fab6e2296cc3f8a95683c0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
