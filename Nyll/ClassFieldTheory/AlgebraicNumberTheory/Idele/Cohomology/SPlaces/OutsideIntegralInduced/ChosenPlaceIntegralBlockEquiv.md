# The integral tensor units at a finite place as an induced module

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields with group `G` and `w₀` a finite place of `K`. Above `w₀` a place of `L` and a local field `E` (`ChosenFinitePlaceLocalizedCompletion`) are chosen, and the decomposition group of that place acts on the integer units `𝒪[E]ˣ`.

- `relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits w₀`: a group isomorphism from the integral unit subgroup `relativeLocalTensorDecompositionIntegralUnitSubgroup w₀` of `(w₀.adicCompletion K ⊗[K] L)ˣ` onto `ChosenFinitePlaceInducedIntegerUnits w₀`, the module induced from the decomposition group to `G` by `𝒪[E]ˣ`.

It is the composite of two imported isomorphisms: one from the integral subgroup to a product of integer-unit groups of completions (`relativeLocalTensorDecompositionIntegralUnitSubgroupEquivPiUnits`), and one from that product to the induced module (`completionProductIntegerUnitsEquivInducedModule`).

The comment speaks of places outside a finite exceptional set, but the definition carries no hypothesis on `w₀`. Equivariance for `G` is not proved in this file. `K` and `L` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/ChosenPlaceIntegralBlockEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `11961bdbf5bb6effa5dcba9871f5ec7800bb52e18c268ecea50ef88df569f1ab`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
