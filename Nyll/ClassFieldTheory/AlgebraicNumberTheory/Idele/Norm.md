# Local-to-global criterion for relative idele norms

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension of number fields. The relative idele group of L over K carries a norm map to the idele group of K. This file proves that an idele a of K is such a norm exactly when each of its local components is a norm from the corresponding local algebra K_v ⊗_K L.

## Main results

- `exists_relativeIdele_norm_eq_of_localTensorPreimages`: suppose we are given units of `w.Completion ⊗[K] L` at every infinite place and of K_v ⊗_K L at every finite place whose determinant norms are the components of a. Suppose also that at cofinitely many finite places the chosen unit and its inverse are integral with respect to a fixed basis (`RelativeBasisIntegralUnitAt`). Then these local data form a relative idele whose norm is a.
- `idele_mem_relativeNorm_range_of_localNorms_with_integralPreimages`: the same conclusion when at the infinite places it is only known that the components lie in `infiniteTensorNormSubgroup`.
- `finiteComponent_mem_localTensorNorm_range_of_mem_relativeNorm_range` and `infiniteComponent_mem_infiniteTensorNormSubgroup_of_mem_relativeNorm_range`: the easy direction, that every component of a global norm is a local norm.
- `mem_relativeIdeleNorm_range_iff_localTensorNorms_native`: for K and L in `Type`, a lies in the range of `RelativeIdeleGroup.norm K L` if and only if every infinite component lies in `infiniteTensorNormSubgroup` and every finite component lies in the range of `localTensorNorm`.
- `mem_relativeIdeleNorm_range_iff_localTensorNorms`: the same criterion for K and L in arbitrary universes.

## Proofs

For the hard direction of the native criterion, the local preimage is chosen to be an integral unit for the local decomposition wherever a_v is a local integral unit, which happens at cofinitely many places. Away from the finite set `integralTensorComparisonBadPlaces` this gives basis integrality, and the assembling theorem applies. The criterion in arbitrary universes is reduced to the native one by moving to the small models `Shrink.{0} K` and `Shrink.{0} L`, through compatible isomorphisms of completions and of relative idele groups.

## Points to watch

- A local norm is the determinant norm from the whole algebra K_v ⊗_K L (the product of the completions of L above v) to K_v, not the norm from a single chosen completion L_w.
- The two criteria assume L/K Galois. The assembling lemmas drop that hypothesis.
- `RelativeIdeleGroup`, `RelativeIdeleGroup.norm`, `localTensorNorm` and `infiniteTensorNormSubgroup` are the library's own constructions, defined in imported files.
- The module heading also mentions the absolute norm on ideles. That norm comes from the imported `Idele.NormCore`, and this file contains only the relative-norm results.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Norm.lean`: the Lean file is the source byte for byte (SHA-256 `b961b246985fe41b9e0c3ab00e52fcb4660d845fea2290c918c233fae402147f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
