# Change of acting group for multiplicative Tate cohomology

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `H` and `G` be finite groups, `e : H ≃* G` an isomorphism, and `A` a commutative group with a multiplicative `G`-action, made into an `H`-module through `e`. The file shows that the low-degree multiplicative Herbrand groups do not change.

## Results

- `tateNorm_compMulEquiv`: the norm for the `H`-action, the product of `e h • a` over `h : H`, equals the product of `g • a` over `g : G`.
- `fixedSubgroupCompMulEquiv`, `normKernelCompMulEquiv`: the subgroups of fixed elements, and the kernels of the norm, for the two actions are isomorphic (they have the same elements).
- `herbrandH0CompMulEquiv`: `HerbrandH0 H A ≃* HerbrandH0 G A`, where `HerbrandH0` is the fixed subgroup modulo the image of the norm.
- `herbrandHMinusOneCompMulEquiv`: for `σ ∈ H`, `HerbrandHMinusOne H A σ ≃* HerbrandHMinusOne G A (e σ)`, where `HerbrandHMinusOne` is the norm kernel modulo the augmentation subgroup attached to the given element.

## Proofs

The subgroups involved coincide as sets of elements of `A`, and the quotients are compared with `quotientMulEquivOfSplit`.

## Points to note

- The module docstring describes the whole localized-completion input of the class formation: finiteness and Galois property of the localization, `H⁰` as the field-norm quotient, `H⁻¹` trivial, and the cardinality and Herbrand quotient equal to the local degree. This file contains only the change-of-group isomorphisms; those local statements are made in other files.
- The degree −1 group depends on the chosen element `σ`, which is transported to `e σ`.
- The action of `H` on `A` is the local instance obtained by composing with `e`, fixed in each statement.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/LocalizedCompletionCohomology/CompMulEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `bf9aba08b37062c98b10308f02a5c20e8500feb730839accf3f3474b02984e98`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
