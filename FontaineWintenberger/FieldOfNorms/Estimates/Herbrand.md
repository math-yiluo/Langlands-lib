# Uniform Herbrand precision below an APF extension

Module `FontaineWintenberger.FieldOfNorms.Estimates.Herbrand`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field and `L/K` a separable APF extension. The file compares the library's Herbrand functions `apfPsi` and `apfPhi` of `L/K` with those of a separable extension `M/K` that embeds in `L` by some `f : M →ₐ[K] L`.

- `apfPsi_le_of_algHom`: for `u ≥ 0`, `apfPsi K M u ≤ apfPsi K L u`.
- `apfPhi_le_of_algHom`: for `u ≥ 0`, `apfPhi K L u ≤ apfPhi K M u`.
- `le_ceil_apfPhi_of_apfPsi_le`: for naturals `N`, `s` with `apfPsi K L N ≤ s`, one has `N ≤ ⌈apfPhi K M s⌉`. The bound `s` depends on `L` only.
- `FiniteIntermediateField.le_ceil_apfPhi_of_apfPsi_le`: the same for finite intermediate fields `E ≤ F` of `L/K`, with `E` as base, under its spectral norm; here the residue field of `K` is perfect.

The first uses `apfPsi_mono_extension` inside a separable closure; the others follow by inverting.

`IsAPF K M` is obtained from `IsAPF.of_algHom` inside the statements.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Estimates/Herbrand.lean` (SHA-256 of the source file `5d108352a0b80c789e36d568a13c80fdf855733a29d24c2d8a9e7df9846678ed`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
