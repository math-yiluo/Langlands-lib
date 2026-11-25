# Relative ideles and the ideles of the extension field

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.BaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension L/K of number fields, this file identifies the library's relative idele group `RelativeIdeleGroup K L` (the file's comments write I_K ⊗_K L; its local factors are unit groups such as (K_w ⊗_K L)ˣ) with the idele group of L. The finite part comes from a restricted-product comparison proved elsewhere. This file treats the archimedean part, matching the infinite places of L above an infinite place w of K with the exact extensions of the absolute value of w, and then assembles both parts.

## Infinite places above w

- `infinitePlaceBelow W`: the restriction of an infinite place of L to K; it is the identity when L = K and transitive in towers. `infinitePlaceCompletionMap_self_apply` and `infinitePlaceCompletionMap_comp_apply` state the same for the maps of completions.
- `infinitePlaceAboveToExtension w W`: an infinite place W above w seen as an absolute value on L restricting exactly to that of w. It is surjective for L/K Galois (`..._surjective_of_isGalois`), by conjugacy of extensions.
- `infinitePlaceAboveEquivExtension w`: for any finite L/K, a bijection between the infinite places of L above w and these exact extensions. Surjectivity passes through the finite normal closure of L/K.

## Archimedean tensor factors

- `infinitePlaceTensorUnitsEquivAbove w`: (K_w ⊗_K L)ˣ ≅ ∏ L_Wˣ over the places W above w, built from the library's local tensor decomposition and Mathlib's completions `InfinitePlace.Completion`. Helpers `infiniteCompletionProductReindexAbove` and `infiniteCompletionProductEquivAbove` reindex the product.
- `infinitePlaceTensorUnitsEquivAbove_localFieldIdeleInclusion`: a unit x of L, placed diagonally, goes to its image in each L_W. A simp lemma says a unit x of K_w goes to x ⊗ 1.
- `infinitePlaceAbovePiMulEquiv`: the product over w of the products of L_Wˣ over the places W above w is isomorphic to the product of L_Wˣ over all infinite places W of L.
- `relativeInfiniteTensorPiMulEquiv` (with `_apply`) and `relativeInfiniteIdeleMulEquiv`: ∏_w (K_w ⊗_K L)ˣ is isomorphic to ∏_W L_Wˣ and to `InfiniteIdeleGroup L`.

## Assembly

- `RelativeLocalIdeleData.toFiniteData` and `relativeLocalIdeleDataSplitMulEquiv`: local idele data split into the unrestricted infinite part and the restricted finite part; multiplication is componentwise (`RelativeFiniteIdeleData.finite_mul`, `RelativeLocalIdeleData.toFiniteData_mul`).
- `relativeIdeleBaseChangeMulEquiv`: `RelativeIdeleGroup K L ≃* IdeleGroup L`, with simp lemmas `..._infinite` and `..._finite` giving its two components.

## Points to watch

- `relativeIdeleBaseChangeMulEquiv` is an isomorphism of groups; no statement about topologies is made here.
- `RelativeIdeleGroup`, `RelativeLocalIdeleData` and the finite comparison `relativeFiniteIdeleMulEquiv` are the library's constructions from other files.
- Exact extensions (`AbsoluteValueExtension`) restrict to the absolute value of w itself, not to an equivalent one.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/BaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `8b6949eb0b0b312425aaac9fbb208444b3dd579b0b323d4671d19bcee9fe7db0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
