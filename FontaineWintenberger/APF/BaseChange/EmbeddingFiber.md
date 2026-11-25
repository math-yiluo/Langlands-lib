# Tate's averaging formula over the embeddings with a given restriction

Module `FontaineWintenberger.APF.BaseChange.EmbeddingFiber`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field (`IsPerfectResidueLocalField K`) and `E ≤ F` finite separable extensions of `K`, not assumed normal. The file proves that the ramification order of an embedding of `E`, compared with the inclusion, is the sum of the orders of its distinct extensions to `F`, divided by the ramification index of `F/E`; first inside a finite Galois extension `Ω/K`, then inside `SeparableClosure K`.

## Definitions

- `EmbeddingRestrictionFiber hEF f`: the `K`-embeddings `τ : F → Ω` whose restriction to `E` is `f`.
- `fixingRestrictionMap hEF s`: for `s` in `Gal(Ω/K)`, the map sending `d` in the fixing subgroup of `E` to `(s·d)|F`, an element of the fibre over `s|E`.
- `restrictedNormalClosureEmbedding K F τ`: an embedding `F → SeparableClosure K` seen as a map into the finite normal closure `finiteGaloisNormalClosure K F`.
- `normalClosureRestrictionFiberEquiv`: the bijection between the fibre taken inside that normal closure and the fibre taken inside `SeparableClosure K`.

## Results

- `fixingRestrictionMap_surjective`, `fixingRestrictionMap_fiber_card`: for `Ω/K` finite and normal, the map is onto, and each of its fibres has as many elements as the fixing subgroup of `F`. Hence `sum_fixingRestrictionMap`: a sum over the fixing subgroup of `E` is that cardinality times the sum over distinct embeddings.
- `sum_embeddingOrder_fixing_restrictions`: the sum over `d` of the orders of `(s·d)|F`, in terms of the function `ramificationOrder` on `Gal(Ω/K)`.
- `embeddingOrder_eq_sum_restrictionFiber`: for `s` in `Gal(Ω/K)`, `embeddingRamificationOrder K (s|E) (incl_E)` equals the sum over `τ` in the fibre of `embeddingRamificationOrder K τ (incl_F)`, divided by `embeddingRamificationIdx K` of the inclusion `E → F`. `embeddingOrder_restriction_eq_sum` states it for any embedding `σ : F → Ω`.
- `embeddingRamificationIdx_isomorphic_square`: the ramification index is unchanged by a commuting square of isomorphisms.
- `closureEmbeddingOrder_restriction_eq_sum`: the same formula for `E ≤ F` finite intermediate fields of `SeparableClosure K` and `σ : F → SeparableClosure K`, with `closureEmbeddingOrder`.
- `closureEmbeddingNumber_restriction_mul_index_eq_sum`: the form with denominators cleared: the index times (`closureEmbeddingNumber` of `σ|E` plus one) equals the sum over the fibre of (`closureEmbeddingNumber` of `τ` plus one), in the extended reals.

## Proofs

The finite formula combines the coset-sum expression of the order with the count of repeated representatives and multiplicativity of the ramification index. The statement in the separable closure is transported from the finite normal closure of `F`.

## What to watch for

- No condition of total ramification is imposed, and the formulas hold in `ℝ≥0∞` or the extended reals, including the infinite value that occurs when an extension equals the inclusion.
- `embeddingRamificationOrder`, `closureEmbeddingOrder`, `closureEmbeddingNumber` and `embeddingRamificationIdx` are the library's notions.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/BaseChange/EmbeddingFiber.lean` (SHA-256 of the source file `5a0e4429d2aac5625df579744f53ec82c54c0362440ca908d300f953a3d89a01`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
