# The first ramification bound of a totally ramified finite subextension

Module `FontaineWintenberger.APF.Elementary.FirstBreak`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field, `L/K` a finite Galois extension with group `G`, and `M` an intermediate field with fixing subgroup `H`, not assumed normal. Write `U u` for the upper ramification groups of `G` on `spectralIntegerRing K L` and `D` for the inertia group.

- `exists_apfRamificationBound_eq_coe_of_fixingSubgroup`: if `H ≠ ⊤` and `H ⊔ D = ⊤`, there is a real `b ≥ 0` with `apfRamificationBound K M = b`, and for `u ≥ -1`, `H ⊔ U u = ⊤` if and only if `u ≤ b`.
- `exists_apfRamificationBound_eq_coe_of_totallyRamified`: the same when `M/K` has degree greater than `1` and is totally ramified.

The proof takes the first upper break of a proper subgroup with full inertia product from the ramification part.

To watch for: total ramification is the hypothesis `he`, stated on the valuation ring of `M` cut out by the spectral valuation of `L`.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Elementary/FirstBreak.lean` (SHA-256 of the source file `3f6f5523092ec408e64c964851f99b69796eebffbce2cd44584977556b0d7b00`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
