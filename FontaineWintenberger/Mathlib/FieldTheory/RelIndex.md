# Relative index of fixing subgroups and relative degree

Module `FontaineWintenberger.Mathlib.FieldTheory.RelIndex`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `Ω/K` be a Galois extension, possibly infinite, and `M ≤ N` intermediate fields. The file compares the relative index of the subgroups of `Gal(Ω/K)` fixing `N` and `M` with the degree of `N` over `M`.

## Main results

- `fixingSubgroup_relIndex_eq_finrank`: `N.fixingSubgroup.relIndex M.fixingSubgroup = Module.finrank M N`, where `N` is regarded as an extension of `M` through `IntermediateField.extendScalars`.
- `fixingSubgroup_relIndex_pos`: if `N` is finite over `M`, this relative index is positive.

## Proof

The fixing subgroup of `M` is identified with `Gal(Ω/M)` by `IntermediateField.fixingSubgroupEquiv`; under this identification the fixing subgroup of `N` corresponds to that of `N` over `M`, whose index is the degree by `IntermediateField.finrank_eq_fixingSubgroup_index`.

## Points to watch

- Both sides are natural numbers, and an infinite index or an infinite degree is represented by `0`; the equality holds in that case too.
- `Ω/K` must be Galois (`IsGalois K Ω`); no finiteness of `Ω/K` is required.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/FieldTheory/RelIndex.lean` (SHA-256 of the source file `aecc99ab5f43aa3bb17c51eec6bd607b7a38474ea7626bd0f247028e79fd755d`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
