# Compositum of two finite abelian extensions

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Given two finite abelian Galois extensions L and E of a field K, this file realizes their compositum inside a chosen separable closure of K, shows that it is again finite abelian Galois, and records the two factor embeddings with their degree bounds.

## Definitions

- `finiteGaloisFieldRange K L`: for L/K finite Galois, the image of L in `SeparableClosure K` under the library's chosen embedding `separableEmbeddingIntoSeparableClosure`; `finiteGaloisFieldRangeEquiv K L` identifies L with it. Instances: it is finite-dimensional and Galois over K.
- `finiteAbelianCompositumField K L E`: the join of the images of L and E in `SeparableClosure K`. Instances: finite-dimensional and `IsAbelianGalois` over K.
- `finiteAbelianCompositumEmbeddingLeft`, `finiteAbelianCompositumEmbeddingRight`: the K-embeddings of L and of E into it.

## Results

- `isAbelianGalois_sup`: in any overfield Ω of K, the join A ⊔ B of two finite-dimensional abelian Galois intermediate fields is abelian Galois over K.
- `finiteAbelianCompositum_embeddingRanges_sup_eq_top`: the images of the two embeddings generate the compositum.
- `finiteAbelianCompositum_finrank_left_le`, `finiteAbelianCompositum_finrank_right_le`: [L : K] and [E : K] are at most the degree of the compositum.

## Proof

For `isAbelianGalois_sup`, restriction of automorphisms gives an injective homomorphism Gal(A ⊔ B / K) → Gal(A/K) × Gal(B/K): an automorphism trivial on both fixes A ⊔ B. The product is commutative, hence so is Gal(A ⊔ B / K). The degree bounds come from injectivity of the embeddings.

## Points to watch

- The compositum is built from the chosen embeddings into `SeparableClosure K`; it is a model of the compositum, not the compositum of two given subfields of a common field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/FiniteAbelianCompositum.lean`: the Lean file is the source byte for byte (SHA-256 `9930f50178ae6fb84d64c675f9aa8a52769c83764deacb9b6397f21ec6f0ef3b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
