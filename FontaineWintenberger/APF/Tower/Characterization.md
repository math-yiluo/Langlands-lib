# Uniqueness of the elementary tower

Module `FontaineWintenberger.APF.Tower.Characterization`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Over a complete discretely valued field `K` with perfect residue field, an elementary tower with APF union is the canonical tower of that union.

Fixed data: a strictly increasing sequence `E n` of finite subfields of the separable closure, strictly increasing reals `i n`, each `E (n+1)` over `E n` an `IsElementaryStep` of level `i n`, and `E 0` fixed by every upper ramification group `G_K^u` with `u > 0`.

- `apfSubgroup_iSup_apfPhi_eq_fixingSubgroup`: at `b n = apfPhi K (E n) (i n)`, the APF product of the union is the fixing subgroup of `E n`.
- `isAPFUpperBreak_apfPhi_of_isElementaryStep`: each `b n` is an upper break of the union.
- `isAPFUpperBreak_iSup_iff_mem_range_apfPhi`: if the union is APF, the upper breaks are exactly the `b n`.
- If moreover the union is infinite over `K` (a `Fact` instance): `apfUpperBreak_iSup_eq_of_isElementaryStep`, `apfElementaryStage_iSup_eq_of_isElementaryStep` (Wintenberger 1.4.2) and `apfElementaryLevel_iSup_eq_of_isElementaryStep` identify the canonical breaks, stages and levels with `b n`, `E n`, `i n`.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §§1.4.1–1.4.2.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/Characterization.lean` (SHA-256 of the source file `3c07cd9c9fed0445743278ce362901b8fc62d8f37dfc6582ef43bac8d7158f25`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
