# Good finite layers in a separable tower

Module `FontaineWintenberger.FieldOfNorms.Layers.GoodTowers`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K ⊆ M ⊆ N ⊆ P` be fields with `M/K` algebraic and `N/M`, `P/N` finite separable. A finite subextension `D` of `P/K` is a good finite layer relative to a middle field (`IsGoodFiniteLayer`) when the multiplication map from the tensor product of that field with `D`, over the pullback of `D`, is bijective. The file shows that finite layers that are good at all three levels of the tower at once are cofinal, as in Wintenberger's paragraph 3.1.1; these are the stages used to compose the covariant maps of norm fields. It is pure field theory.

## Main results

* `isGoodFiniteLayer_of_tensor`: let `E` be a finite subextension of `N/K` and `C` an intermediate field of `M/K` equal to the pullback of `E`, with an algebra structure of `C` on `E` compatible with the inclusions. If some `M`-algebra isomorphism `e : M ⊗_C E ≃ N` satisfies `e (m ⊗ d) = m · d`, then `IsGoodFiniteLayer K M E`. Goodness thus does not depend on how the coefficient field is presented.
* `FiniteIntermediateField.pullback_tower`, `FiniteIntermediateField.pullbackLayer_tower`: for a finite subextension `D` of `P/K`, pulling back to `N` and then to `M` gives the pullback of `D` to `M`, as intermediate fields and as finite layers. `FiniteIntermediateField.pullbackTo_tower` says the two inclusions into `D` agree.
* `exists_goodFiniteLayer_tower_ge`: every finite subextension `E` of `P/K` lies in a finite `D` such that `D` is good relative to `N`, `D` is good relative to `M`, and the pullback of `D` to `N` is good relative to `M`.
* `exists_goodFiniteLayer_tower_ge_pair`: the same with `D` containing two prescribed finite subextensions.

## Proofs

`exists_finiteIntermediateField_tensor_descent_tower` supplies a finite `C` in `M/K` and `D` over `C` with the three multiplication isomorphisms, with `D ∩ M = C` and `(D ∩ N) ∩ M = C`. `FiniteIntermediateField.pullback_eq_of_inf` identifies `C` with the two pullbacks, the pullback of `D` to `N` is `finiteDescentIntersection D` by definition, and `isGoodFiniteLayer_of_tensor` converts each isomorphism into goodness.

## Remarks

`IsGoodFiniteLayer`, `FiniteIntermediateField.pullback` and `FiniteIntermediateField.pullbackLayer` are the library's notions, defined in `FontaineWintenberger.FieldOfNorms.Layers.NormPairs`. The cofinality theorems require `M/K` algebraic and both steps of the tower finite and separable.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3, paragraph 3.1.1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Layers/GoodTowers.lean` (SHA-256 of the source file `639c33bc9a9c52f3abb6ee386360c55cdaacecf351daf6fe45b8d83c67eef57a`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
