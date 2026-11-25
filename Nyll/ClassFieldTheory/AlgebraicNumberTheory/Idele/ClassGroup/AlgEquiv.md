# Transport of adeles, ideles and idele classes along field isomorphisms

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library's relative adele ring of a finite extension L/K of number fields is 𝔸_K ⊗_K L (`RelativeAdeleRing K L`), with relative ideles its units. This file transports relative adeles, ideles, idele classes and norm subgroups along isomorphisms of fields. It treats three cases: an isomorphism L ≃ M over K, an isomorphism of number fields over ℚ, and compatible isomorphisms of both fields of an extension.

## Changing the top field

For `e : L ≃ₐ[K] M`:

- `relativeAdeleCongr e`: 𝔸_K ⊗ L ≃ 𝔸_K ⊗ M, a ⊗ x ↦ a ⊗ e(x). `relativeIdeleCongr e` and `relativeIdeleClassCongr e` are the induced maps on units and on classes; principal ideles and the principal subgroups correspond. For σ ∈ Aut(L/K), `relativeIdeleCongr σ` is the Galois action (`relativeIdeleCongr_eq_smul`).
- `relativeIdeleCongr_norm`, `relativeIdeleClassCongr_ideleClassNorm`: the determinant norm to the ideles of K, and the induced class norm to the idele classes of K, are unchanged. Hence `ideleClassNorm_range_algEquiv` and `ideleClassNorm_index_algEquiv`: the norm subgroups of the idele class group of K, and their indices, agree.
- `RelativeIdeleGroup.classEmbedding_relativeIdeleClassCongr`: compatibility with class embeddings along a further f : M → N.

## Number fields isomorphic over ℚ

For `e : K ≃ₐ[ℚ] M`:

- `adeleCongr e`: a ring isomorphism of adele rings, defined as `relativeAdeleCongr` over ℚ conjugated by the base-change isomorphisms `relativeAdeleBaseChangeRingEquiv`. It preserves the diagonal (`adeleCongr_algebraMap`).
- `finitePlaceCongr e`: the induced bijection of finite places. On finite coordinates `adeleCongr` acts by the completion maps `finitePlaceAdicCompletionCongrHom` (`adeleCongr_finiteComponent`).
- `ideleCongr e` and `ideleClassCongr e`: transport of ideles and idele classes. `ideleCongr` acts on finite components by the completion maps and preserves normalized local orders (`ideleCongr_localOrder`), ideles integral at all finite places, principal ideles, and the subgroup defining ideal classes (`ordinaryIdealClassSubgroup_map_congr`); `ideleClassCongr` preserves that subgroup's image in idele classes.
- Naturality: the relative-to-ordinary comparison over ℚ turns `relativeIdeleCongr` and the Galois action into `ideleCongr`, on ideles and on idele classes (`relativeIdeleBaseChangeMulEquiv_smul_congr`, `relativeIdeleClassBaseChangeMulEquiv_smul_congr` and companions).
- `rationalIdeleExtension_eq_ideleCongr` and its adele and class versions: when M ≅ ℚ, scalar extension from ℚ to M equals the transport.

## Changing both fields

For `eK : K ≃ₐ[ℚ] K'` and `eL : L ≃ₐ[ℚ] L'` compatible with the algebra maps:

- `relativeAdeleCongrOfAlgEquiv`, `relativeIdeleCongrOfAlgEquiv`, `relativeIdeleClassCongrOfAlgEquiv`: the induced isomorphisms, preserving principal elements.
- Norm compatibility: `relativeAdeleCongrOfAlgEquiv_norm`, `relativeIdeleCongrOfAlgEquiv_norm`, `relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm`.
- `relativeIdeleClassNorm_range_map_congrOfAlgEquiv`, `ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv`: `ideleClassCongr eK` maps the norm subgroup from L onto that from L'.
- `ordinaryIdeleClassNormQuotientCongrOfAlgEquiv`: the resulting isomorphism C_K / N(C_L) ≅ C_K' / N(C_L').

## Points to watch

- All transports are isomorphisms of rings or groups; no topological statement is made.
- `adeleCongr` is built through relative adeles over ℚ, not place by place; only its finite coordinates are described here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/AlgEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `11fa8e95146ed076abac6c4fa5ba59446d8f1a657e4c9c5b23f693343719ed51`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
