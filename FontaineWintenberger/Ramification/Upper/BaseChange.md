# Ramification groups over a finite intermediate base

Module `FontaineWintenberger.Ramification.Upper.BaseChange`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete ultrametric normed field, `E` a normed algebraic extension whose spectral integer ring over `K` is a discrete valuation ring, and `M` an intermediate field finite over `K`. The integer ring of `E` over `M` is the same subring, so ramification data of `E ≃ₐ[M] E` can be read inside `E ≃ₐ[K] E`.

- `finiteBase_ramificationOrder`: an element of `M.fixingSubgroup` has the same `ramificationOrder` over `M` as over `K`.
- `finiteBase_lowerReal_map_fixingSubgroupEquiv`, `finiteBase_lower_map_fixingSubgroupEquiv`: the lower group over `M` at a real, or integer, index is the image of the lower group over `K` cut down to `M.fixingSubgroup`.
- `finiteBase_lowerReal_map_restrictScalars`, `finiteBase_lower_map_restrictScalars`: inside `E ≃ₐ[K] E` it is the intersection with `M.fixingSubgroup`.
- `finiteBase_lower_zero_eq_top`: if `M.fixingSubgroup` lies in inertia, inertia over `M` is everything.
- `finiteBase_upper_map_fixingSubgroupEquiv`: for `E/K` finite and `v ≥ -1`, the upper group at `v` of `M.fixingSubgroup` maps onto that of `E ≃ₐ[M] E`.

The upper statement concerns the subgroup's own upper numbering, not an intersection with upper groups of `E ≃ₐ[K] E`.

Reference: Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Upper/BaseChange.lean` (SHA-256 of the source file `69fbc36946ef899c582acddea2a968d2a5df31d9432b9d2663bc1fc8a22fd3b8`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
