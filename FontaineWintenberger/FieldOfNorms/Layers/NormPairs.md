# Good finite layers and their norm identities

Module `FontaineWintenberger.FieldOfNorms.Layers.NormPairs`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K ⊆ M ⊆ N` be fields. A finite subextension `D` of `N/K` is a good finite layer when it descends `N/M`: with `C = D ∩ M`, the multiplication map `M ⊗_C D → N` is an isomorphism. The file defines these layers, proves that they are cofinal when `M/K` is algebraic and `N/M` is finite separable, and proves that on an inclusion `D ≤ D'` of good layers the norm from `D'` to `D` restricts to the norm from `D' ∩ M` to `D ∩ M`. It is pure field theory.

## Main definitions

For `D : FiniteIntermediateField K N`:

* `FiniteIntermediateField.pullback K M D`: the preimage of `D` in `M`, finite over `K`; `FiniteIntermediateField.pullbackLayer` is the same as a `FiniteIntermediateField K M`. `FiniteIntermediateField.pullbackTo` is its inclusion into `D`, and `FiniteIntermediateField.overPullback` is `D` as an intermediate field of `N` over its pullback. Algebra and finiteness instances are registered.
* `FiniteIntermediateField.tensorMap K M D`: the multiplication map `M ⊗_C D → N`, with `C` the pullback.
* `IsGoodFiniteLayer K M D`: this map is bijective. `goodFiniteLayerTensorEquiv` is the resulting isomorphism.
* `goodFinitePairTensorEquiv`: for good layers `D ≤ D'` with pullbacks `C ≤ C'`, the `D`-algebra isomorphism `D ⊗_C C' ≃ D'`, `d ⊗ a ↦ d · a` (`goodFinitePairTensorEquiv_tmul`).

## Main results

* `FiniteIntermediateField.pullback_eq_of_inf`, `isGoodFiniteLayer_of_descent`: a field `D` between `C ⊆ M` and `N`, finite over `K`, with `D ∩ M = C`, has pullback `C`; if it is also linearly disjoint from `M` with `M ⊗_C D → N` surjective, it is good.
* `exists_goodFiniteLayer_ge`, `exists_goodFiniteLayer_ge_pair`: if `M/K` is algebraic and `N/M` is finite separable, every finite subextension of `N/K` (or every pair) lies in a good finite layer.
* `finrank_goodFiniteLayer`: for a good layer, `[D : C] = [N : M]`.
* `linearDisjoint_goodFiniteLayer`: a good layer is linearly disjoint from `M` over its pullback.
* `goodFinitePair_norm`: for good `D ≤ D'` and `a` in `C'`, `FiniteIntermediateField.norm D D'` of `a` equals `FiniteIntermediateField.norm` from `C'` to `C` of `a`, viewed in `D`.
* `goodFinitePair_sup_eq`: for good `D ≤ D'`, the layer `D'` is the compositum of `D` and the image of `C'`.

## Proofs

Cofinality comes from `exists_finiteIntermediateField_tensor_descent`. The pair isomorphism is injective because `D ⊗_C C'` is a field, and surjective by the degree count `[C':C] = [D':D]`. The norm identity is `norm_eq_of_tensorEquiv` applied to it.

## Remarks

`IsGoodFiniteLayer` is the library's own notion, a property of `D` alone: the coefficient field is always the pullback `D ∩ M`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Layers/NormPairs.lean` (SHA-256 of the source file `d5ede070630dc158b0ea1f5362058618ed0703536a3b698f549850a33a0844cb`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
