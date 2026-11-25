# The directed family of finite intermediate fields

Module `FontaineWintenberger.Mathlib.FieldTheory.FiniteIntermediateField`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a field extension `L/K`, the file introduces the set of all finite intermediate fields as an index set, with composita, norm maps for inclusions, images under embeddings, and gluing of algebra homomorphisms defined on the finite layers. No normality is assumed.

## Main definitions

- `FiniteIntermediateField K L`: the subtype of intermediate fields of `L/K` that are finite-dimensional over `K`, ordered by inclusion.
- `FiniteIntermediateField.bottom`, `sup`: the image of `K`, and the compositum of two finite intermediate fields. Instances: the type is nonempty and directed, as is every upper set `Set.Ici E`.
- `norm E F h : F →* E`, for `E ≤ F`: the field norm of `F` over `E`, a monoid homomorphism (`normUnits` on units). It vanishes only at `0` (`norm_eq_zero_iff`), is the identity for `E = F` (`norm_self`) and is transitive (`norm_norm`).
- `map i E`, `equivMap i E`: for a `K`-embedding `i : L → M`, the image of `E` in `M` and the isomorphism of `E` onto it.
- `mapOrderIso e`: for a `K`-isomorphism `e : L ≃ M`, the order isomorphism between the two families; `mapIci i E` is the map induced on the upper set of `E`.
- `liftAlgHom f hf : M →ₐ[L] N`: for an algebraic extension `M/L` and `L`-algebra homomorphisms `f Q : Q → N` on all finite intermediate fields `Q`, compatible with inclusions, the homomorphism on `M` that they define.

## Main results

- `tendsto_Ici_inclusion`, `map_Ici_inclusion_atTop`: for `E ≤ F`, the inclusion of `Set.Ici F` in `Set.Ici E` is cofinal and carries the filter `atTop` to `atTop`.
- `equivMap_norm`: `equivMap i E (norm E F h x) = norm (map i E) (map i F) _ (equivMap i F x)`.
- `tendsto_mapIci`: for an isomorphism `e`, `mapIci e E` is cofinal.
- `directed_toSubalgebra`, `exists_mem`, `iSup_toSubalgebra_eq_top`: the finite intermediate fields form a directed family of subalgebras; in an algebraic extension every element lies in one, so their supremum is the whole extension.
- `liftAlgHom_apply`, `liftAlgHom_comp_val`: the glued map restricts to `f Q` on each `Q`.
- `algHom_ext`, `liftAlgHom_unique`: an algebra homomorphism from an algebraic extension is determined by its restrictions to the finite intermediate fields, so the glued map is unique.

## Proofs

The norm is Mathlib's `Algebra.norm` for `F` regarded as an extension of `E` through `IntermediateField.extendScalars`. Gluing uses `Subalgebra.iSupLift`.

## Points to watch

- `FiniteIntermediateField` is the library's own notion, an `abbrev` for a subtype; the underlying field of `E` is `E.val`.
- `norm` takes the proof of `E ≤ F` as an argument and is only multiplicative.
- The gluing statements require an algebraic extension; the rest holds for any field extension.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/FieldTheory/FiniteIntermediateField.lean` (SHA-256 of the source file `938484817d6fcb2b07a08fa2ba323096a6df47f9fdf2e834a34930b47d4c73b6`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
