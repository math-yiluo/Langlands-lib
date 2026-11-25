# Stabilization of Herbrand functions on finite stages

Module `FontaineWintenberger.APF.Tower.Herbrand`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field and `E ≤ L` intermediate fields of its separable closure. If `E` contains the stage `apfFiniteStage K L u`, then `E` and `L` have the same APF data up to the parameter `u`.

- `apfSubgroup_eq_of_apfFiniteStage_le`: `apfSubgroup K E u = apfSubgroup K L u`.
- `apfIndex_eq_of_apfFiniteStage_le`: `apfIndex K E v = apfIndex K L v` for `0 ≤ v ≤ u`.
- `apfPsi_eq_of_apfFiniteStage_le`: `apfPsi K E v = apfPsi K L v` for `v ≤ u`.
- `IsAPF.exists_finiteIntermediateField_apfPsi_eq`: for an abstract separable APF extension `L/K` and a real `u`, there is a finite intermediate field `E` such that every finite intermediate field `F ≥ E` satisfies `apfPsi K F v = apfPsi K L v` for all `v ≤ u`.

The second and third follow from the first by integrating the index.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.4 and the proof of Corollary 3.3.6.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/Herbrand.lean` (SHA-256 of the source file `2c469eff2061aa0e9e50cfb7ad2267d7494965d3421a1b0b442366413d85cf32`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
