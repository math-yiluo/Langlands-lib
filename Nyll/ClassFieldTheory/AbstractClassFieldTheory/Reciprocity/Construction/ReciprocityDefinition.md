# Definition of the abstract reciprocity map

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The definition of the reciprocity map in the abstract class field theory of the library. Let `L/K` be finite and normal, and let `σ` be a Frobenius element of `L̃/K`, where `L̃` is the maximal unramified extension of `L`. Its fixed field `Σ` is finite over `K`, and the reciprocity value of `σ` is the class of `N(Σ/K)(π_Σ)` in `A_K / N(L̃/K) A_L̃`, for a prime element `π_Σ` of `Σ`.

## Main definitions and results

All of them assume `G` a compact Hausdorff topological group, `L/K` normal and `G(L/K)` finite.

- `frobeniusFixedIntermediateField`: `Σ` as a finite intermediate field of `L̃/K`.
- `frobeniusFixedField_absoluteFinite`: if `K` has finite absolute degree, so does `Σ`.
- `reciprocityValueOfPrime A K L σ π`: the class of `N(Σ/K)(π)` in `MaximalUnramifiedNormQuotient A K L`, for any `π ∈ A_Σ`.
- `reciprocityMap A v K L`: the map from the Frobenius elements of `L̃/K` to `A_K / N(L̃/K) A_L̃`. It sends `σ` to `reciprocityValueOfPrime` at the chosen prime element of `Σ` (`chosenPrimeElement`). `reciprocityMap_eq_chosenPrime` states this definitionally.

## Watch for

- `reciprocityValueOfPrime` places no condition on `π`. That its value is the same for every prime element, and hence equals `reciprocityMap`, is not proved in this file. The module docstring says it is proved separately, from the unit-cohomology axiom.
- The map is defined on the library's Frobenius elements (`FrobeniusElements`), with values in the quotient by the infinite norm group `N(L̃/K) A_L̃`. It is not yet defined on `G(L/K)` or with values in `A_K / N(L/K) A_L`.
- `K` must have finite absolute degree (`FiniteAbstractField`) for the map, while the value with an explicit prime only needs finite residue structure.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityDefinition.lean`: the Lean file is the source byte for byte (SHA-256 `bab862c5586a9a19c256c18d8c11404ac4c8790a309476d8a4a621ef8d2fe17f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
