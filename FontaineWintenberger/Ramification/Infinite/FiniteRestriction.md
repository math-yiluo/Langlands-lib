# Infinite upper ramification and abstract finite Galois subextensions

Module `FontaineWintenberger.Ramification.Infinite.FiniteRestriction`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The infinite upper ramification groups `upperRamificationGroupInfinite K Ω u` are defined through finite Galois intermediate fields of `Ω`. This file transfers the comparison to a finite Galois extension `E/K` given as a separate field with `K → E → Ω` a scalar tower, not as an intermediate field.

For `u ≥ −1`:

- `restrictNormal_mem_upperRamificationGroup_of_finite`: if `σ` lies in `upperRamificationGroupInfinite K Ω u`, then `σ.restrictNormal E` lies in the upper group of `E ≃ₐ[K] E` computed on `spectralIntegerRing K E`.
- `exists_lift_upperRamificationGroup_of_finite`: if `Ω/K` is Galois and the residue field of `K` is perfect, every element of that finite upper group is the restriction of an element of the infinite one.
- `restrictNormalHom_map_upperRamificationGroup_of_finite`: under the same hypotheses, restriction maps the infinite upper group onto the finite one.

The proofs replace `E` by its image in `Ω` (private definitions) and use invariance of upper groups under isomorphism (`upperRamificationGroup_map_autCongr`).

## What to watch for

`K` is a complete discretely valued field in the library's sense.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Infinite/FiniteRestriction.lean` (SHA-256 of the source file `0cb86f75d5081a1821119463d38305cdd7759946e778f7e9546cca86e663ce7c`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
