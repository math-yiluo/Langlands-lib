# Archimedean tensor factors as local blocks

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.InfinitePlaceTensorBlock`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields and w an infinite place of K. The adele library uses the concrete completion `w.Completion` (Mathlib's completion at an infinite place). The library's local tensor decomposition instead uses the completion of the underlying absolute value `w.1`. This file identifies the two completions and base-changes the identification to K_w ⊗_K L. For L/K Galois, it then connects the archimedean component of a relative idele to a local tensor block, compatibly with the action of Gal(L/K) on the factor L.

## Definitions and results

- `infinitePlaceCompletionAlgEquiv w`: the K-algebra isomorphism from `w.Completion` to `w.1.Completion`, built from `InfinitePlace.Completion.equiv`.
- `infinitePlaceCompletionAlgEquiv_algebraMap`: for an infinite place w of L above v, these isomorphisms commute with the completion maps K_v → L_w on both sides.
- `infinitePlaceLocalTensorAlgEquiv w`: the base change K_w ⊗_K L ≃ `LocalTensorAlgebra` of `w.1`. `..._tmul` computes it on pure tensors. `infinitePlaceLocalTensorUnitsEquiv` is the induced isomorphism on units.
- `infinitePlaceLocalTensorAlgEquiv_conjugation` and `infinitePlaceLocalTensorUnitsEquiv_smul`: these maps commute with conjugation by σ ∈ Gal(L/K) on the factor L.
- `infinitePlaceTensorUnitsEquivLocalPlaceBlock` (L/K Galois): for an extension u of `w.1` to L, a multiplicative isomorphism (K_w ⊗_K L)ˣ ≃ `LocalPlaceBlock` at u. It is the units comparison followed by `localTensorUnitsEquivLocalPlaceBlock`.
- `infinitePlaceTensorUnitsEquivLocalPlaceBlock_smul`: this isomorphism is equivariant for all of Gal(L/K). The action on the block is the one from the imported local-block files, set up with `decompositionGroupLocalUnitsAction`.

## Proofs

The tower compatibility is proved by density. The set where the two maps agree is closed, and they agree on the image of K. The equivariance statements are checked on pure tensors and then composed with `localTensorUnitsEquivLocalPlaceBlock_smul`.

## Points to watch

- The block isomorphism takes the nontriviality of `w.1` as an explicit argument `hw`. It is not derived from w being an infinite place.
- `LocalTensorAlgebra`, `LocalPlaceBlock` and the Galois actions on them are the library's own constructions, defined in other files. The algebra structures on the completions at u are fixed by local instances.
- The comparisons on tensors need neither that K and L are number fields nor that L/K is finite. Only the block statements assume L/K Galois.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/InfinitePlaceTensorBlock.lean`: the Lean file is the source byte for byte (SHA-256 `79a74cdc70b7e913763bf68fe29b9907b51383f84cf749ef69caf58bc6cd424d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
