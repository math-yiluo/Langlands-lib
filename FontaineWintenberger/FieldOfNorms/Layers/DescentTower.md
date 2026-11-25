# Simultaneous finite descent in a separable tower

Module `FontaineWintenberger.FieldOfNorms.Layers.DescentTower`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `M/K` be an algebraic field extension and `M ⊆ N ⊆ P` a tower of finite separable extensions. The file shows that the finite descent of `P/M` to a finite level `D/C` can be chosen so that it also descends the two steps of the tower: with `B = D ∩ N`, the three multiplication maps `M ⊗_C D → P`, `M ⊗_C B → N` and `N ⊗_B D → P` are isomorphisms. Such `D` are cofinal among the finite subextensions of `P/K`. This is the algebraic content of Wintenberger's paragraph 3.1.1 for a tower; no valuation is involved.

## Main definitions

For a tower `C ⊆ M ⊆ N ⊆ P` and an intermediate field `D` of `P/C`:

* `tensorEquivOfLinearDisjoint D hD hsurj`: if `D` is finite over `C`, linearly disjoint from `M`, and the multiplication map `M ⊗_C D → P` is surjective, that map is an `M`-algebra isomorphism.
* `finiteDescentIntersection D`: the preimage of `D` in `N`, an intermediate field of `N/C`; `finiteDescentIntersection_map` identifies its image in `P` with `D ∩ N`. `finiteDescentIntersectionTo` is its inclusion into `D`, which is registered as an algebra structure with scalar-tower instances.
* `finiteDescentIntersectionTensorEquiv`: `M ⊗_C (D ∩ N) ≃ N`, when `D` is linearly disjoint from `M` and contains the generator of a power basis `b` of `N/M`.
* `finiteDescentUpperTensorEquiv`: `N ⊗_(D ∩ N) D ≃ P`, under the same hypotheses together with surjectivity of `M ⊗_C D → P`.

## Main results

* `linearDisjoint_finiteDescentIntersection`: `D ∩ N` is linearly disjoint from `M` when `D` is.
* `finrank_finiteDescentIntersection`: `[D ∩ N : C] = [N : M]`.
* `finrank_finiteDescentUpper`: `[D : D ∩ N] = [P : N]`.
* `exists_finiteIntermediateField_tensor_descent_tower`: for a finite subextension `D₀` of `P/K` there are a finite subextension `C` of `M/K` and `D` between `C` and `P`, finite over `K`, containing `D₀`, linearly disjoint from `M` with `D ∩ M = C`, such that `B = D ∩ N` is finite over `K`, linearly disjoint from `M` with `B ∩ M = C`, and the three tensor maps above are isomorphisms given by multiplication.
* `exists_common_finiteIntermediateField_tensor_descent_tower`: the same with `D` containing two prescribed finite subextensions.

## Proofs

The existence theorem applies `exists_finiteIntermediateField_tensor_descent` to `P/M` and to the compositum of `D₀` with `K(β)`, where `β` generates `N/M`. The lower map is then onto, and injective by linear disjointness. The upper map is onto because `M ⊗_C D → P` is, and injective by the degree count `[D:B] = [P:N]`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3, paragraph 3.1.1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Layers/DescentTower.lean` (SHA-256 of the source file `59e8633d3083602212393cfa15eac0a28a0a63a9f7467a6510bca47217cae26b`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
