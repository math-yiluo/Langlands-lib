# Idele-class norms in a tower of number fields

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a tower of finite extensions of number fields `K ⊆ M ⊆ L`, the file keeps the bottom adele ring `𝔸_K` fixed and presents the adeles of `M` as `𝔸_K ⊗[K] M` and those of `L` as `(𝔸_K ⊗[K] M) ⊗[M] L`. This gives a genuine determinant norm `C_L → C_M` whose composite with `C_M → C_K` is the norm of `L/K`, and a right-exact sequence of norm quotients with the resulting bound on their orders.

## Tower presentation

- `TowerRelativeAdeleRing K M L = (𝔸_K ⊗[K] M) ⊗[M] L`, with the tensor-cancellation isomorphism `towerRelativeAdeleRingEquiv` onto the one-step model `𝔸_K ⊗[K] L` (and its forms `towerRelativeAdeleAlgEquiv` over `𝔸_K`, `towerRelativeAdeleFlatten`, `towerRelativeAdeleUnflatten`, with formulas on pure tensors).
- `TowerRelativeIdeleGroup K M L`: its unit group, with `principalIdele` (the diagonal `Lˣ`), `principalSubgroup` and `ClassGroup`; `classGroupEquiv` identifies this class group with the one-step relative class group `RelativeIdeleGroup.ClassGroup K L`.

## Norms

- `TowerRelativeIdeleGroup.norm`: the determinant norm `Algebra.norm` over `𝔸_K ⊗[K] M`, from tower ideles of `L` to relative ideles of `M`.
- `norm_transitive_flatten`: composing with the norm from `M` to `K` gives the one-step norm of `L/K` after flattening.
- `norm_fieldInclusion`, `norm_principalIdele`: on the diagonal copy of `L` the norm is the field norm `Algebra.norm M`; hence `classNorm : C_L → C_M` is defined on class groups.

## The norm-quotient sequence

- `IntermediateClassNormQuotient K M L`: `C_M` modulo the image of `classNorm`; `towerCompositeClassNorm` is `C_L → C_M → C_K`, equal to the one-step class norm under `classGroupEquiv`, with the same image (`towerCompositeClassNorm_range_eq`); hence `towerCompositeClassNormQuotientEquiv` identifies `TowerCompositeClassNormQuotient K M L` (`C_K` modulo its image) with `RelativeIdeleGroup.ClassNormQuotient K L`.
- `intermediateToCompositeNormQuotient`, from `IntermediateClassNormQuotient K M L` to `TowerCompositeClassNormQuotient K M L` and induced by the norm `C_M → C_K`, and the projection `compositeToBaseNormQuotient` from the latter to `RelativeIdeleGroup.ClassNormQuotient K M`. The sequence is exact in the middle (`intermediateToCompositeNormQuotient_range_eq_ker`) and the second map is surjective.
- `towerCompositeClassNormQuotient_card_le_mul`, `ideleClassNormQuotient_card_le_mul`: if the two outer quotients are finite, then the order of the middle one (respectively of `RelativeIdeleGroup.ClassNormQuotient K L`) is at most the product of their orders; finiteness of the middle quotient is deduced from exactness.

## Points to watch

- The class groups of `M` and `L` are the library's relative presentations built from `𝔸_K`, not Mathlib's idele class groups; `C_K` is `IdeleClassGroup K`.
- The cardinality bound carries finiteness of the two outer quotients as instance hypotheses; the file does not prove it.
- The sequence is only right-exact; nothing is said about injectivity of the first map.
- The file declares global instances (priority 100) making `𝔸_K ⊗[K] M` an `M`-algebra through the right factor and `𝔸_K ⊗[K] L` an `M`-algebra through `M → L`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/Tower.lean`: the Lean file is the source byte for byte (SHA-256 `9577b9f3f27b620c64109c17463cbf736c5347a47da0f30156ea64e2a597e45a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
