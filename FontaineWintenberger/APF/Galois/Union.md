# The APF subgroups of an increasing union

Module `FontaineWintenberger.APF.Galois.Union`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field and `D 0 ≤ D 1 ≤ …` an increasing sequence of intermediate fields of `SeparableClosure K`.

The file has one theorem, `apfSubgroup_iSup_eq_iInf`: for every real `u`,

`apfSubgroup K (⨆ n, D n) u = ⨅ n, apfSubgroup K (D n) u`.

In words, with `L` the union of the `D n`: `G_L · G_K^u` is the intersection of the groups `G_M · G_K^u` for `M = D n`.

The proof has two steps. The fixing subgroup of the union is the intersection of the fixing subgroups. Then the supremum with the closed normal subgroup `G_K^u` commutes with the intersection of a decreasing sequence of closed subgroups of a compact group (`Subgroup.iInf_sup_eq_iInf_sup_of_isClosed`, from the library's additions to Mathlib).

To watch for: the family is indexed by the natural numbers and assumed monotone (`hD`); no hypothesis on `u` or on the residue field is made.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.2.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Galois/Union.lean` (SHA-256 of the source file `1995e4e7fb97e0dafde93df3053b2b36e65a8f8e59e60eb219f5f5beacdb9ef9`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
