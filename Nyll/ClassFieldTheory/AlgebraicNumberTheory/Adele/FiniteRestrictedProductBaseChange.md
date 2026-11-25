# Finite relative ideles as finite ideles of the extension

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.FiniteRestrictedProductBaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields. A finite relative idele gives, at each finite place w of K, a unit of K_w ⊗_K L. This file identifies the group of such families, restricted in a fixed K-basis of L, with the finite idele group of L. At each w it splits K_w ⊗_K L into the completions L_W at the places W above w, then collects all W into one product over the finite places of L.

## Main definitions and results

- `finitePlaceTensorUnitsEquivAboveAdic w`: a multiplicative isomorphism from (K_w ⊗_K L)ˣ onto the product of the groups L_Wˣ over the places W above w. It is the library's local tensor decomposition, followed by a comparison with the adic completions of L and a reindexing by the places above w. `..._localFieldIdeleInclusion` says that the diagonal image of x ∈ Lˣ goes to the image of x in each L_W.
- `relativeFiniteTensorPiMulEquiv`: the resulting isomorphism ∏_w (K_w ⊗_K L)ˣ ≃ ∏_W L_Wˣ of unrestricted products.
- `relativeLocalTensorDecompositionIntegralUnitAt_iff_aboveAdic`: a unit of K_w ⊗_K L satisfies the library's predicate `RelativeLocalTensorDecompositionIntegralUnitAt` iff each of its components above w is a unit of the valuation ring of L_W.
- `eventually_finitePlace_iff_eventually_all_above`: a property holds at almost all finite places of L iff, for almost all finite places w of K, it holds at every place above w.
- `RelativeFiniteIdeleData`: finite relative ideles. Such an idele is a family of units x_w of K_w ⊗_K L such that, for almost all w, the coordinates of x_w and of x_w⁻¹ in the basis `relativeExtensionBasis` are integral.
- `relativeFiniteIdeleEquiv`: a bijection between `RelativeFiniteIdeleData` and `FiniteIdeleGroup L`. `relativeFiniteIdeleMulEquiv` is the same map as a group isomorphism.

Helpers handle reindexing and flattening of products, and the two directions of the bijection.

## Proofs

The first direction adds a trivial infinite part and applies the imported theorem `relativeIdele_finiteComponent_localTensorDecompositionIntegralUnit_of_notMem` outside the finite set `relativeIdeleLocalTensorDecompositionSupport`. The converse uses the finite set `integralTensorComparisonBadPlaces`: outside it, integrality of basis coordinates is equivalent to integrality in the local tensor decomposition. Moving cofinite conditions between the places of L and those of K uses that only finitely many places lie above each w.

## Points to watch

- The group structure `relativeFiniteIdeleDataGroup` on `RelativeFiniteIdeleData` is transported along the bijection. It is not defined coordinatewise.
- Restrictedness is defined through a fixed K-basis of L, not through the valuation rings of the L_W. The file shows that the two conditions give the same group.
- Only finite places appear. The comparison is algebraic, and no topology is considered.
- L/K is assumed finite, not Galois.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/FiniteRestrictedProductBaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `c6283628506da62c646096f53fe442e6c764deccfe69315fbcefa749a8df3d0b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
