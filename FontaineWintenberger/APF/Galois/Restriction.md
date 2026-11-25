# The APF subgroup of a subextension of a Galois extension

Module `FontaineWintenberger.APF.Galois.Restriction`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field, `E` an intermediate field of `SeparableClosure K` that is Galois over `K`, possibly infinite, and `M` an intermediate field of `E`, not assumed normal.

The file has one theorem, `apfSubgroup_map_eq_comap_upperRamificationGroupInfinite`: for `u ≥ -1`, the APF subgroup `apfSubgroup K (M.map E.val) u` of the image of `M` in the separable closure is the preimage, under the restriction homomorphism from the absolute Galois group of `K` to `Gal(E/K)`, of `Gal(E/M) ⊔ Gal(E/K)^u`. Here `Gal(E/M)` is the fixing subgroup of `M` and `Gal(E/K)^u` is `upperRamificationGroupInfinite K E u`.

The proof writes the fixing subgroup of the image of `M` as the preimage of that of `M`, which contains the kernel of restriction, then applies the Galois case `apfSubgroup_eq_comap_upperInfinite` and surjectivity of restriction.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.2.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Galois/Restriction.lean` (SHA-256 of the source file `5ed73df3a06ac50960205f49c058fa1270026983003b29d38ce1dce7d3b173f7`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
