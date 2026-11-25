# Good finite layers for finite Galois extensions

Module `FontaineWintenberger.FieldOfNorms.Layers.GaloisGood`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K ⊆ M ⊆ N` be fields with `N/M` finite Galois. A finite subextension `D` of `N/K` is a good finite layer (`IsGoodFiniteLayer K M D`) when, with `C = D ∩ M` its pullback to `M`, the multiplication map `M ⊗_C D → N` is bijective. The file shows that a `D` which is stable under `Gal(N/M)` and contains a primitive element of `N/M` is good, that `D/C` is then Galois-theoretically a copy of `N/M`, and that such stable good layers are cofinal. This is pure field theory.

## Main definition

* `galoisFiniteLayerRestrict K M N D hD`: for `D` with `σ(D) = D` for every `σ` in `N ≃ₐ[M] N` (hypothesis `hD`), the group homomorphism from `N ≃ₐ[M] N` to the automorphisms of `D` over its pullback `FiniteIntermediateField.pullback K M D`, by restriction (`coe_galoisFiniteLayerRestrict`). It is defined without the Galois assumption.

## Main results

Let `N/M` be finite Galois, `D` stable as above.

* `galoisFiniteLayerRestrict_fixedField`: the fixed field in `D` of the range of the restriction homomorphism is the bottom field, that is, the pullback `C`.
* `galoisFiniteLayerRestrict_injective`: if `α ∈ D` and `M(α) = N`, the restriction homomorphism is injective.
* `finrank_galois_stableFiniteLayer`: under the same hypotheses, `[D : C] = [N : M]`.
* `isGoodFiniteLayer_of_galois_stable`: under the same hypotheses, `D` is a good finite layer.
* `exists_galois_stable_goodFiniteLayer_ge`: if moreover `N/K` is algebraic, every finite subextension `E` of `N/K` lies in a finite `D` that is good, stable under `N ≃ₐ[M] N`, and contains an `α` with `M(α) = N`.
* `exists_galois_stable_goodFiniteLayer_ge_pair`: two finite subextensions lie in a common stable good `D`.

## Proofs

Elements of `D` fixed by all of `Gal(N/M)` lie in `M`, hence in `C`. Artin's theorem (`IntermediateField.finrank_fixedField_eq_card`) then gives `[D:C]` as the order of the range, which is `[N:M]` by injectivity. The multiplication map `M ⊗_C D → N` is onto because `α` is in its image, and it is bijective by equality of dimensions over `M`. For cofinality, `D` is the normal closure in `N` over `K` of the compositum of `E` with `K(α)`, with `α` a primitive element of `N/M`; it is stable under every `K`-automorphism of `N` (`IntermediateField.map_normalClosure_eq`).

## Remarks

* Stability is asked only under automorphisms of `N` over `M`; `N` is not assumed normal over `K`, and the layer `D` produced need not be normal over `K` in the absolute sense, only its own normal closure inside `N`.
* `IsGoodFiniteLayer` and `FiniteIntermediateField.pullback` are the library's notions, from `FontaineWintenberger.FieldOfNorms.Layers.NormPairs`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Layers/GaloisGood.lean` (SHA-256 of the source file `0ca1b2017286f9a2cfb859456984d257c73e5f16a624c3bbe3e5fa11afc06f80`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
