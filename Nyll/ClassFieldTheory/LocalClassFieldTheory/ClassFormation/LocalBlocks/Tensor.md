# The tensor-product realization of a local block

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension, `v` a nontrivial absolute value on `K` with completion `K_v`, and `w` a chosen extension of `v` to `L`. The algebra `K_v ⊗[K] L`, the factor at `v` of `𝔸_K ⊗[K] L`, carries the Galois action on the second factor. The file shows that its unit group is equivariantly isomorphic to the induced local block `LocalPlaceBlock v hv w`, via the product of the completions of `L` above `v`.

## Main definitions

- `LocalTensorAlgebra v` is `K_v ⊗[K] L`; `localTensorConjugation v σ` is the `K_v`-algebra automorphism `1 ⊗ σ`, and `localTensorUnitsAction` the induced action on units.
- `conjugateCompletionRingEquiv w σ` (and `conjugateExtensionCompletionRingEquiv`): the ring isomorphism from the completion at `w ∘ σ` to the completion at `w` induced by `σ`; it fixes the embedded `K_v`.
- `localTensorEvaluation`: the `K_v`-algebra map `b ⊗ x ↦ b·x` into the algebraic localization `LocalizedCompletion v w`.
- `localTensorOrbitHom`: `z ↦ (g ↦ evaluation of (1 ⊗ g) z)`, a homomorphism from the units of `K_v ⊗[K] L` to the block.
- `inducedRightCosetCoordinates`: for any group `G`, subgroup `H` and commutative group `B` on which `H` acts by group automorphisms, the induced module `{f : G → B | f(hg) = h • f(g)}` is isomorphic to the functions `H\G → B`, by restriction to chosen coset representatives.
- `rightCosetExtensionEquiv`: for `H` the decomposition group of `w`, a bijection from `H\G` to the extensions of `v` to `L`, sending a coset to `w ∘ (representative)`.
- `completionProductUnitsEquivLocalPlaceBlock`: the product of the completion unit groups over all extensions `w'` of `v` is isomorphic to the block.
- `localTensorUnitsEquivLocalPlaceBlock`: `(K_v ⊗[K] L)ˣ ≃* LocalPlaceBlock v hv w`, composed from `localTensorUnitsEquivCompletionProduct` and the previous isomorphism.

## Main results

- `localTensorOrbitHom_smul`: orbit evaluation turns conjugation on the tensor factor into the action on the induced module.
- `localTensorUnitsEquivLocalPlaceBlock_eq_orbitHom_apply`: the isomorphism coincides with orbit evaluation.
- `localTensorUnitsEquivLocalPlaceBlock_smul`, `localTensorUnitsEquivLocalPlaceBlock_symm_smul`: the isomorphism and its inverse are `Gal(L/K)`-equivariant.

## Proofs

Surjectivity of `rightCosetExtensionEquiv` is transitivity on extensions, `absoluteValueConjugacy`. The isomorphism is compared with orbit evaluation on coset representatives; equivariance follows from that of orbit evaluation.

## Points to note

- The block takes values in `LocalizedCompletion v w`, the algebraic localization, reached from the metric completion through `localizedCompletionEquivCompletion`.
- The intermediate product isomorphisms depend on coset representatives chosen by `Quotient.out` and carry no equivariance statement; only the composite with the tensor algebra is shown equivariant.
- The induced module uses the convention `f(hg) = h • f(g)`, hence right cosets `H\G`. Neither cyclicity of `Gal(L/K)` nor normality of the decomposition group is assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/LocalBlocks/Tensor.lean`: the Lean file is the source byte for byte (SHA-256 `f6ef7148846c4c2c58f97659c2d4a3956cced228b9e66f534cb0cf38147e2774`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
