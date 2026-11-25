# Indices of products with a normal subgroup

Module `FontaineWintenberger.Mathlib.GroupTheory.Index`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Lemmas on finite index and relative indices `A.relIndex B` of subgroups of a group `G`, in Mathlib's namespace `Subgroup`.

## Main results

For a homomorphism `f : G′ → G`:

- `finiteIndex_iff_comap_of_range`: if the range of `f` has finite index, `J ≤ G` has finite index iff its preimage does.
- `comap_sup_eq_of_normal_right_of_le_range`: if `U` is normal and `A` lies in the range of `f`, then `f⁻¹(A) ⊔ f⁻¹(U) = f⁻¹(A ⊔ U)`.

For subgroups `A`, `B` and a normal subgroup `U` of `G`:

- `relIndex_eq_index_of_sup_eq_top`: if `A ⊔ U = ⊤`, then `A.relIndex U = A.index`.
- `relIndex_sup_left_of_normal_right`: `A.relIndex (A ⊔ U) = A.relIndex U`.
- `relIndex_sup_sup_normal`: `(A ⊔ U).relIndex (B ⊔ U) = (A ⊔ U).relIndex B`.
- `sup_inf_eq_sup_inf_of_le_of_normal`: if `A ≤ B`, then `(A ⊔ U) ⊓ B = A ⊔ (U ⊓ B)`.
- `relIndex_sup_sup_eq_inf`: if `A ≤ B`, then `(A ⊔ U).relIndex (B ⊔ U) = (A ⊔ (U ⊓ B)).relIndex B`.

## Points to watch

- Indices are natural numbers, an infinite index being `0`.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/GroupTheory/Index.lean` (SHA-256 of the source file `574ee6dbc0b3346e3a34502290f4d96b12c4a822982f4b5ff9e70b2d2834fcf0`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
