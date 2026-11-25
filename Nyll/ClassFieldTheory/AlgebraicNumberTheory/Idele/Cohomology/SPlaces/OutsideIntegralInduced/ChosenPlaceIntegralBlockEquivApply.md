# The integral induced block inside the local block

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockEquivApply`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields and `w₀` a finite place of `K`. Two imported maps leave the integral unit subgroup of `(w₀.adicCompletion K ⊗[K] L)ˣ`. One goes to the module induced by the integer units of the chosen local field, followed by its inclusion into the local block of field units. The other is the field-unit equivalence of `(w₀.adicCompletion K ⊗[K] L)ˣ` with that local block.

- `chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_equiv_apply`: for `x` in the integral unit subgroup, applying `relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits` and then the inclusion `chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock` gives the same element as applying `finitePlaceTensorUnitsEquivLocalPlaceBlock` to `x` viewed in `(w₀.adicCompletion K ⊗[K] L)ˣ`.

The proof compares the two elements through their coordinates on the right cosets of the decomposition group (`inducedRightCosetCoordinates`, which is injective); the coordinates then agree by definition. `K` and `L` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/ChosenPlaceIntegralBlockEquivApply.lean`: the Lean file is the source byte for byte (SHA-256 `87184443f722fb4af74a8571dd5ee2e38e9361ae28842f687d3b5a1eb75f78cd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
