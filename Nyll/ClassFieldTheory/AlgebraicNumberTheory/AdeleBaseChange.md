# Base change of adeles: 𝔸_K ⊗_K L ≅ 𝔸_L

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields. This file builds a ring isomorphism between the library's relative adele ring `RelativeAdeleRing K L` = 𝔸_K ⊗_K L and Mathlib's adele ring `NumberField.AdeleRing (𝓞 L) L` of L. It then shows that the idele isomorphism constructed earlier is the map this ring isomorphism induces on units. The module comment says the additive structure is needed later, to transport determinant norms in a tower of fields.

## Local pieces

- `finitePlaceTensorRingEquivAboveAdic w`: for a finite place w of K, a ring isomorphism from K_w ⊗_K L onto the product of Mathlib's adic completions L_W of L, for W above w. `..._tmul` says that a ⊗ x goes, at W, to the image of a in L_W times x.
- `infinitePlaceTensorRingEquivAbove w`: the same at an infinite place, onto the completions `W.Completion` above w, with the analogous `..._tmul` (using Mathlib's `LiesOver.completionMap`).
- `relativeFiniteTensorPiRingEquiv` and `relativeInfiniteTensorPiRingEquiv`: the resulting isomorphisms between the unrestricted products over the places of K and those over the places of L.

## Main results

- `relativeLocalTensorDecompositionIntegralAt_iff_aboveAdicRing`: the library's integrality predicate at w holds iff every coordinate above w lies in the valuation ring of L_W.
- `relativeAdele_eventually_aboveAdicIntegral`: for every relative adele, all coordinates above w are integral for almost every w.
- `relativeAdeleBaseChangeRingEquiv`: the ring isomorphism 𝔸_K ⊗_K L ≃ 𝔸_L, with inverse `adeleToRelativeAdele`.
- `relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul` and `..._infiniteComponent_tmul`: the image of a ⊗ x, for a ∈ 𝔸_K and x ∈ L, has component at W equal to the image of a at the place below W, times x.
- `relativeAdeleBaseChangeRingEquiv_fieldInclusion`: 1 ⊗ x goes to the diagonal adele of x.
- `relativeIdeleBaseChangeMulEquiv_eq_ringUnits`: the imported isomorphism `relativeIdeleBaseChangeMulEquiv` agrees, through `IdeleGroup.equivAdeleRingUnits`, with the map on units induced by `relativeAdeleBaseChangeRingEquiv`. `finitePlaceTensorUnitsEquivAboveAdic_coe` and `relativeFiniteTensorPiMulEquiv_coe` are the local forms of this.
- `relativeIdeleBaseChangeMulEquiv_principalIdele`: for x ∈ Lˣ, the relative principal idele of x goes to the principal idele of x in the ideles of L.

## Proofs

Outside the finite set `integralTensorComparisonBadPlaces`, basis integrality is equivalent to integrality in each L_W. This gives restrictedness in both directions, using the coefficient support in the forward one. `eventually_finitePlace_iff_eventually_all_above` moves cofinite conditions between the places of K and of L.

## Points to watch

- The isomorphism is one of rings only. The file states nothing about topologies or about compatibility with an 𝔸_K-module structure. Compatibility with L is shown only on the diagonal copy of L.
- The construction uses the library's local tensor decomposition and the fixed K-basis of L. Its finite components are identified with Mathlib's adic completions of L through `finitePlaceExtensionAdicCompletionRingEquiv` and reindexed by `finitePlaceExtensionEquivAbove`.
- L/K need not be Galois.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/AdeleBaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `698f5c6a77a0dc65a15e894001ca9f4131be354b6a0a6eb1226c4214eb95de39`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
