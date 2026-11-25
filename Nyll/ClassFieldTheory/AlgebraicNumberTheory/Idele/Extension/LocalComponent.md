# Local components of relative adeles and ideles

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension `L/K` of number fields, with the adeles of `L` modelled as `𝔸_K ⊗_K L`, the file defines the component of a relative adele or idele at a place `v` of `K`. This component lies in `K_v ⊗_K L`. The file also shows that the component of the determinant norm at `v` is the determinant norm of the component.

## Main declarations

- `infiniteAdeleComponentAlgHom v`, `finiteAdeleComponentAlgHom v`: evaluation `𝔸_K → K_v` at an infinite or finite place, as `K`-algebra maps.
- `relativeAdeleInfiniteComponent v`, `relativeAdeleFiniteComponent v`: their base changes `𝔸_K ⊗_K L → K_v ⊗_K L`, with `_tmul` lemmas.
- `RelativeIdeleGroup.infiniteComponent v`, `RelativeIdeleGroup.finiteComponent v`: the induced maps on units, from relative ideles to `(K_v ⊗_K L)ˣ`.
- `map_norm_tensorProduct_baseChange`: for a `K`-algebra map `f : A → B` of nontrivial commutative `K`-algebras and `z ∈ A ⊗_K L`, `f (N_A z) = N_B ((f ⊗ id) z)`. It is proved by evaluating the norm polynomial `normPolynomial` from the file on Galois norms. Here `K` and `L` need not be number fields.
- `localTensorNorm v`: the determinant norm `(K_v ⊗_K L)ˣ → K_vˣ` at a finite place.
- `RelativeIdeleGroup.finiteComponent_norm`, `RelativeIdeleGroup.infiniteComponent_norm`: the `v`-component of the relative idele norm is the determinant norm of the `v`-component of the relative idele.
- `localIdeleInclusion`, `localFieldIdeleInclusion` and their archimedean versions `infiniteLocalIdeleInclusion`, `infiniteLocalFieldIdeleInclusion`: the maps `K_vˣ → (K_v ⊗_K L)ˣ` and `Lˣ → (K_v ⊗_K L)ˣ`. The `_inclusion` and `_principalIdele` lemmas compute the components of included and principal ideles with them.

## Points to watch

- The local norms here are determinant norms on `K_v ⊗_K L`; their splitting into norms of the completions of `L` above `v` is not done in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/LocalComponent.lean`: the Lean file is the source byte for byte (SHA-256 `37bcc865d57d7a003075e7776780bfca65d6ffc6965bb3c74a7286f44f80777a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
