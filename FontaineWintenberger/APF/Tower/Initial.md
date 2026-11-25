# The unramified and tame initial stages of the elementary tower

Module `FontaineWintenberger.APF.Tower.Initial`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a separable APF extension `L/K` with `IsPerfectResidueLocalField K`, Wintenberger's fields `K₀` and `K₁` are the finite intermediate fields `apfMaximalUnramified K L` and `apfMaximalTame K L` defined earlier. The file records their ramification properties.

- `apfMaximalUnramified_ramificationIdx`: `K₀/K` has ramification index `1`.
- `apfMaximalTame_relative_ramificationIdx`: the ramification index of `K₁` over `K₀` equals the degree `[K₁ : K₀]`, so the step is totally ramified.
- `apfMaximalTame_relative_finrank`: `[K₁ : K₀]` equals the ramification index of `K₁` over `K`.
- `apfMaximalTame_relative_finrank_coprime`: `[K₁ : K₀]` is prime to the residue characteristic.
- `IsElementaryStep.apfRamificationBound_eq`: for finite subfields `E < F` of the separable closure of a complete discretely valued field, if `F/E` is an elementary step of level `i`, then `apfRamificationBound` of `F` over `E` (with the spectral norm on `E`) equals `i`. The inclusion must be strict.

Ramification indices are those of the maximal ideals of the spectral integer rings.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.4.1(a)–(b).

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/Initial.lean` (SHA-256 of the source file `7a457f1d71397cc9c06fb71ed62063a07c0baf5ba29d0ce18cbce73c01133896`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
