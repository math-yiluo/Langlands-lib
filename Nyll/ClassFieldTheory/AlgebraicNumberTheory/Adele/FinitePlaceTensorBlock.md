# Finite-place tensor factors as local blocks

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.FinitePlaceTensorBlock`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension of number fields and v a finite place of K, given as a height-one prime of 𝓞 K. This file links two completions of K at v. The first is the concrete completion `v.adicCompletion K` used in the idele restricted product. The second is the completion at the v-adic absolute value `HeightOneSpectrum.adicAbv K v`, which the library's local tensor decomposition uses. The file shows that the comparison between the two respects the action of Gal(L/K) on the factor L of K_v ⊗_K L. It is the finite-place counterpart of `InfinitePlaceTensorBlock`.

## Results

- `finitePlaceLocalTensorAlgEquiv_conjugation`: the algebra isomorphism `finitePlaceLocalTensorAlgEquiv`, from `LocalTensorAlgebra` of the absolute-value completion to `v.adicCompletion K ⊗[K] L`, commutes with conjugation by σ ∈ Gal(L/K) on L.
- `finitePlaceLocalTensorUnitsEquiv_smul` and `finitePlaceLocalTensorUnitsEquiv_symm_smul`: the induced isomorphism on unit groups, and its inverse, are equivariant for these conjugation actions.
- `finitePlaceTensorUnitsEquivLocalPlaceBlock`: for an extension w of the v-adic absolute value to L, a multiplicative isomorphism from (K_v ⊗_K L)ˣ to `LocalPlaceBlock` at w. It is the inverse comparison followed by `localTensorUnitsEquivLocalPlaceBlock`.
- `finitePlaceTensorUnitsEquivLocalPlaceBlock_smul`: this isomorphism is equivariant for the whole group Gal(L/K). The action on (K_v ⊗_K L)ˣ is through L. The action on `LocalPlaceBlock` is the one from the imported local-block files, built from the action of the decomposition group of w on the units of the completion at w.

## Proofs

The algebra statement is checked on pure tensors, where it holds by definition, and extends by additivity. The unit statements follow from it. The final equivariance combines the inverse statement with `localTensorUnitsEquivLocalPlaceBlock_smul`.

## Points to watch

- `LocalTensorAlgebra`, `LocalPlaceBlock`, `finitePlaceLocalTensorAlgEquiv` and the Galois actions are the library's own constructions, defined in other files.
- The block depends on the chosen extension w. The algebra structures on the completions at w are fixed by local instances in this file.
- The nontriviality of the v-adic absolute value, which the block construction needs, is supplied by `RayClass.adicAbv_isNontrivial`.
- The first three theorems do not need L to be a number field, nor L/K to be finite or Galois.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/FinitePlaceTensorBlock.lean`: the Lean file is the source byte for byte (SHA-256 `166e43f1990e0d78be35c02df733983cfb8677f1c9e58e469953b60facae69e7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
