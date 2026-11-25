# Ramification profiles of finite elementary towers

Module `FontaineWintenberger.APF.Tower.FiniteCriterion`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Over a complete discretely valued field `K` with perfect residue field, the file determines the APF products `apfSubgroup` of the last field of a finite elementary tower.

Data: a monotone tower `E : Fin (m+1) → FiniteIntermediateField K (SeparableClosure K)`, strictly increasing levels `i n`, each `E n.succ` over `E n.castSucc` an `IsElementaryStep` of level `i n`, and `E 0` fixed by every `G_K^u`, `u > 0`. Put `b n = apfPhi K (E n.castSucc) (i n)`.

- `strictMono_apfPhi_finite_elementary_tower`: `b` is strictly increasing.
- `apfSubgroup_eq_fixingSubgroup_of_finite_elementary_step`: for `u > b n`, the product of `E n.succ` at `u` is its fixing subgroup.
- `finite_elementary_tower_profiles`: for the last field, the product at `b n` is the fixing subgroup of `E n.castSucc`; for `u > b n` below all later `b k` it is that of `E n.succ`; for `u > 0` below all `b k` it is that of `E 0`.

`m = 0` is allowed.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, Remark 1.4.2.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/FiniteCriterion.lean` (SHA-256 of the source file `74c98d25ec232fe4bd8a508a518537ee8ff8d57e74bd59ea3348e48460d7f406`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
