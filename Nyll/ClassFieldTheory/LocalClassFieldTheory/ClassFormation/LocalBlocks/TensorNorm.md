# The norm image of a local tensor factor

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.TensorNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension, `v` a nontrivial absolute value on `K` with completion `K_v`, and `w` a chosen extension of `v` to `L`, with algebraic localization `L_w = LocalizedCompletion v w`. The completion tensor-product theorem writes `K_v ⊗[K] L` as the product of the completions of `L` above `v`, and conjugation identifies each factor with `L_w`. The file deduces that the image of the norm of the `K_v`-algebra `K_v ⊗[K] L` on units is exactly the norm subgroup `N(L_wˣ) ⊆ K_vˣ`. The docstring describes this as the bridge between the local cohomology calculation and multiplicative weak approximation.

## Definitions

- `localTensorDetNorm v`: the norm `Algebra.norm K_v` on `(K_v ⊗[K] L)ˣ`, as a homomorphism to `K_vˣ`; `localTensorNormSubgroup v` is its range.
- `rightCosetCompletionAlgEquiv`: for a right coset `q` of the decomposition group, the `K_v`-algebra isomorphism from the completion at the corresponding extension of `v` to `L_w`, given by conjugation followed by the identification of the completion with the localization.
- `localTensorUnitsEquivChosenCoordinates`: `(K_v ⊗[K] L)ˣ` is isomorphic to the functions from the right cosets to `L_wˣ`.
- `decompositionRightCosetsFinset`: the finite set of all right cosets, packaged so that products do not depend on a chosen `Fintype` instance.

## Results

- `normUnits_rightCosetCompletionAlgEquiv`, `normUnits_completionProductUnitsEquivRightCosets`: transporting a coordinate to `L_w` preserves its norm to `K_v`.
- `localTensorDetNorm_eq_prod_chosenCoordinates`: the norm of a unit `z` of `K_v ⊗[K] L` is the product over the right cosets of the field norms of its coordinates in `L_w`.
- `localTensorNormSubgroup_eq_localNormSubgroup`: `localTensorNormSubgroup v = localNormSubgroup K_v L_w`.

## Proofs

The product formula comes from `RelativeIdeleGroup.localNorm_units_eq_prod`, which expresses the norm on the tensor algebra through its completion components, reindexed by `rightCosetExtensionEquiv`. For the equality of subgroups, a norm from the tensor algebra is the norm of the product of the coordinates; conversely, `N(y)` is the norm of the unit whose coordinate is `y` at the trivial coset and `1` elsewhere.

## Points to note

No nonarchimedean or local-field hypothesis is made; `v` is any nontrivial absolute value. The norm subgroup on the right is that of the algebraic localization `LocalizedCompletion`, which serves as the model of `L_w`, and the equality holds for every choice of `w`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/LocalBlocks/TensorNorm.lean`: the Lean file is the source byte for byte (SHA-256 `7c8d5560b70369f01eb4da2c7fcc461776fe904640a2bac9353ea197898d43cf`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
