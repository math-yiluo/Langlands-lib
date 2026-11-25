# Equivariance of the field-unit equivalence on integral tensor units

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockTensorSmul`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields with group `G` and `w₀` a finite place of `K`. The imported equivalence `finitePlaceTensorUnitsEquivLocalPlaceBlock` identifies `(w₀.adicCompletion K ⊗[K] L)ˣ` with the local block at the chosen place above `w₀`, and `G` acts on the integral unit subgroup `relativeLocalTensorDecompositionIntegralUnitSubgroup w₀` by restriction.

- `finitePlaceTensorUnitsEquivLocalPlaceBlock_restricted_smul`: for `τ ∈ G` and `x` in the integral unit subgroup, applying the equivalence to `τ • x` gives `τ` applied to the image of `x`.

The restricted action on the subgroup agrees with the action on `(w₀.adicCompletion K ⊗[K] L)ˣ` (`relativeLocalTensorDecompositionIntegralUnitSubgroupAction_coe`), so the statement reduces to the imported equivariance `finitePlaceTensorUnitsEquivLocalPlaceBlock_smul`. `K` and `L` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/ChosenPlaceIntegralBlockTensorSmul.lean`: the Lean file is the source byte for byte (SHA-256 `cd893663ff39ee3b66c4a550e16cb93ba0651c10a35691b0640f9f1e840a47b6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
