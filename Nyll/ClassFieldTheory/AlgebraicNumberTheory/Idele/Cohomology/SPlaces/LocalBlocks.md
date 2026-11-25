# The local blocks of a relative S-idele

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.LocalBlocks`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields with group `G` and `S` a finite set of finite places of `K`. The unrestricted factors of a relative `S`-idele sit at every infinite place of `K` and at the finite places in `S`. The file packages them into one finite dependent family and identifies it `G`-equivariantly with the induced local blocks of the local tensor decomposition.

## Main definitions and results

- `chosenInfinitePlaceAbove v`: an infinite place of `L` above the infinite place `v` of `K`, chosen by `Classical.choose`; `chosenInfinitePlaceAbove_comap` says it restricts to `v`.
- `RelativeUnrestrictedSPlaceIndex S`: the index type `InfinitePlace K ⊕ S`.
- `relativeUnrestrictedSPlaceDatum S`: the local data at each index: at an infinite place, its absolute value and the chosen place above; at `v ∈ S`, the `v`-adic absolute value and the imported choice `chosenFinitePlaceExtension`.
- `RelativeUnrestrictedSPlaceFactor S i`: the unit group `(K_v ⊗[K] L)ˣ`, with `K_v` the archimedean or `v`-adic completion; `RelativeUnrestrictedSPlaceFactors S` is the product over all indices, and `relativeUnrestrictedSPlaceFactorsAction` lets `G` act componentwise on the factor `L`.
- `relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily`: a group isomorphism from the product of these factors to `LocalBlockFamily (relativeUnrestrictedSPlaceDatum S)`, built from the imported local isomorphisms at infinite and finite places; `relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily_smul` says it is equivariant for the whole group `G`.
- `relativeUnrestrictedSPlaceFactorsEquivProd`: the same family rewritten as a pair: the family of `(v.Completion ⊗[K] L)ˣ` over the infinite places `v` and the family of `(v.adicCompletion K ⊗[K] L)ˣ` over `v ∈ S`.

## Points to watch

- The places of `L` above the places of `K` are choices; the local blocks depend on them.
- Apart from `chosenInfinitePlaceAbove` and `chosenInfinitePlaceAbove_comap`, the fields `K` and `L` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/LocalBlocks.lean`: the Lean file is the source byte for byte (SHA-256 `2bf241d288ccd107dcf1e99d48fa6264838d80e74835296baed7c5320ee03d32`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
