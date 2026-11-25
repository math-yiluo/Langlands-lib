# Integral local factors of the relative idele group

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralLocalFactor`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields and w a finite place of K. The library's local tensor decomposition identifies K_w ⊗_K L with the product of the completions of L at the extensions of the w-adic absolute value to L. This file turns the projections onto these factors into ring homomorphisms. It then defines the subgroup of tensor units that are integral in every factor, together with their inverses, and identifies it with the product of the unit groups of the valuation rings. So the integrality condition used for the restricted product is a subgroup condition, independent of any choice of coordinates.

## Definitions and results

- `finitePlaceLocalTensorDecompositionComponentRingHom w wL`: the projection from K_w ⊗_K L to the completion of L at wL, as a ring homomorphism. It agrees with the imported map `finitePlaceLocalTensorDecompositionComponent`, which therefore preserves 0 and addition.
- `finitePlaceLocalTensorDecompositionUnitsComponent` and `finitePlaceLocalTensorDecompositionUnitsEquiv w`: the projections on units, and the isomorphism from (K_w ⊗_K L)ˣ onto the product of the unit groups of these completions.
- `conjugateExtensionCompletionRingEquiv_norm_eq` and `..._mem_integers_iff`: a K-automorphism σ of L induces an isomorphism from the completion at the conjugate extension to the completion at wL. This isomorphism preserves the norm, and so the valuation ring when the absolute value is nonarchimedean. Both are stated for any field K with a real absolute value, which the second requires to be nonarchimedean.
- `finitePlaceLocalTensorDecompositionComponent_scalarTensorConjugation`: the component at wL of σ·x is the image of the component of x at the conjugate extension.
- `relativeLocalTensorDecompositionIntegralAt_scalarTensorConjugation` and `relativeLocalTensorDecompositionIntegralUnitAt_smul`: the integrality predicates are stable under every σ.
- `relativeLocalTensorDecompositionIntegralUnitAt_iff`: a unit x satisfies `RelativeLocalTensorDecompositionIntegralUnitAt` iff every component of x is a unit of its valuation ring.
- `relativeLocalTensorDecompositionIntegralUnitSubgroup w`: the subgroup of such units. `mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff` identifies membership with the predicate. `relativeLocalTensorDecompositionIntegralUnitSubgroupAction` restricts the action of K-automorphisms of L to this subgroup.
- `relativeLocalTensorDecompositionIntegralUnitSubgroupEquivProduct` and `...EquivPiUnits`: the subgroup is isomorphic to the product of the unit groups of the valuation rings of the completions. The first version uses the product subgroup `FinitePlaceLocalTensorDecompositionIntegralUnitProduct`, the second the unit groups of the valuation rings themselves.

## Proofs

The component maps are composites of the imported decomposition `completionTensorDecomposition_left` and the base change `relativeFinitePlaceLocalTensorAlgEquiv`. Galois stability is checked on pure tensors and then follows from the norm preservation of the conjugation isomorphism.

## Points to watch

- The factors are indexed by absolute-value extensions of the w-adic absolute value, not by prime ideals of 𝓞 L.
- The predicates `RelativeLocalTensorDecompositionIntegralAt` and `RelativeLocalTensorDecompositionIntegralUnitAt` and the action on tensor units are the library's own, defined in imported files.
- L/K is not assumed Galois. The acting group is the group of K-automorphisms of L.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/IntegralLocalFactor.lean`: the Lean file is the source byte for byte (SHA-256 `fa3ecc0ba8532370112171b8406aae3b031f3ab59fc76c5dff058f234598d4cf`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
