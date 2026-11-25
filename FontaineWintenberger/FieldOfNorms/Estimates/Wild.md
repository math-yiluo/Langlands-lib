# Additive norm congruence above wild inertia

Module `FontaineWintenberger.FieldOfNorms.Estimates.Wild`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field, `Ω/K` a finite Galois extension with a compatible ultrametric norm and residue characteristic `p`, and `P` the first lower ramification group of `Ω/K`.

`FiniteIntermediateField.integerNorm_add_congruence_of_wild_field`: let `E ≤ F` be intermediate fields with `E` containing the fixed field of `P`, and `b` real with `b ≤ apfRamificationBound E F`. Then for all `x`, `y` in `spectralIntegerRing K F`, the element `N(x + y) − N(x) − N(y)`, with `N = integerNorm E F`, lies in the power `⌈(p − 1)/p · b⌉` of the maximal ideal of `spectralIntegerRing K E`.

Proof: the fixing subgroup of `E` is a `p`-group, so `relative_prime_field_chain` gives a chain of cyclic Galois steps of degree `p` from `E` to `F`. Each step is totally ramified (`wildField_step_ramificationIdx_eq_finrank`) with ramification bound at least that of `F/E` (`apfRamificationBound_le_step_of_finiteGalois`). So `integerNorm_prime_add_congruence_of_bound` applies at every step with the same `b`, and `integerNorm_add_congruence_tower` composes the steps.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Estimates/Wild.lean` (SHA-256 of the source file `37648fed135da85bfc12ab0aa26079609675bd9a7b36219f6ef5e2276c2b2567`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
