# Base change of idele-class norms along a pushout square

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.BaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file considers a pushout square of finite extensions of number fields, `K → M`, `K → L`, `M → N`, `L → N` with `N = M ⊗[K] L` (`Algebra.IsPushout K M L N`), and builds the maps on relative adeles, ideles and idele class groups that relate the extension `L/K` to the extension `N/M`. Keeping the bottom adele ring `𝔸_K` fixed turns the norm square into a base-change identity for determinant norms. It is meant for the step of adjoining roots of unity.

## Main definitions and results

- `pushoutTowerAdeleEquiv`: an algebra isomorphism over `𝔸_K ⊗[K] M` between the tower presentation `(𝔸_K ⊗[K] M) ⊗[M] N` of the adeles of `N` and `BaseChangedRelativeAdeleRing K M L = (𝔸_K ⊗[K] M) ⊗[K] L`.
- `pushoutTowerAdeleInclusion`, `pushoutTowerIdeleInclusion`: the induced ring map from the relative adeles of `L/K` to the tower adeles of `N/M`, sending `a ⊗ x` to `(a ⊗ 1) ⊗ algebraMap L N x`, and the map on unit groups; principal ideles of `L` go to principal ideles of `N`.
- `pushoutTowerIdeleNorm_inclusion`: the relative norm of `N/M` applied to the image of an idele `a` of `L` equals the image in the ideles of `M` of the norm of `a` for `L/K`. `pushoutTowerClassNorm_inclusion` is the same square on idele class groups (via `pushoutTowerClassInclusion`).
- `pushoutNormQuotientMap`: the map from `RelativeIdeleGroup.ClassNormQuotient K L` to the norm quotient of `C_M` for `N/M`, induced by the inclusion `C_K → C_M`.
- `ideleClassNorm_classInclusion`: on `C_K`, inclusion into `C_M` followed by the norm is `c ↦ c ^ [M:K]`.
- `changeIntermediateClassGroupEquiv`: the class group of `N` presented through `M` is identified with the one presented through `L`, preserving the composite norm to `K`.
- `pushoutNormQuotientNormBack`: the map back, induced by the norm `C_M → C_K`; `pushoutNormQuotientNormBack_comp_map` says that the composite is the `[M:K]`-th power map.
- `pushoutNormQuotientMap_injective_of_pow_injective`: if `q ↦ q ^ [M:K]` is injective on `RelativeIdeleGroup.ClassNormQuotient K L`, then `pushoutNormQuotientMap` is injective.

## Proofs

The idele norm square uses that `Algebra.norm` is invariant under the algebra isomorphism `pushoutTowerAdeleEquiv` and compatible with base change of the coefficient ring (`map_norm_tensorProduct_baseChange`); the class-level statements descend it through the quotients.

## Points to watch

- The injectivity theorem carries the injectivity of the `[M:K]`-th power map on the norm quotient as the hypothesis `hpow`; the file does not prove when it holds.
- The adeles and ideles of `L` are the library's relative objects `RelativeAdeleRing K L = 𝔸_K ⊗[K] L` and its units, and the adeles of `N` are taken in the tower presentation over `M`, not Mathlib's adele ring of `L` or `N`. The norm is the determinant norm over the adele ring.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/BaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `d405339df5efd661dc651adae14e00d04263bc02dcd5366ba180c776259987cb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
