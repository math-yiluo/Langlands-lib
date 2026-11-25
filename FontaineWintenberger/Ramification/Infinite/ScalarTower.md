# Infinite upper ramification in an abstract scalar tower

Module `FontaineWintenberger.Ramification.Infinite.ScalarTower`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Compatibility of the infinite upper ramification groups with restriction, for a Galois subextension `M/K` given as a separate field in a scalar tower `K → M → Ω`, not as an intermediate field. Here `K` is a complete discretely valued field in the library's sense and `u ≥ −1`.

- `AlgEquiv.restrictNormal_restrictScalars_comm`: for a tower `K → C → M → Ω` with `M` normal over `K` and over `C`, and `σ` a `C`-automorphism of `Ω`, restricting scalars to `K` and restricting to `M` commute.
- `restrictNormal_mem_upperRamificationGroupInfinite_tower`: if `σ` lies in `upperRamificationGroupInfinite K Ω u`, then `σ.restrictNormal M` lies in `upperRamificationGroupInfinite K M u`.
- `exists_lift_upperRamificationGroupInfinite_tower`: if `Ω/K` is Galois and the residue field of `K` is perfect, every element of the upper group of `M/K` is such a restriction.
- `restrictNormalHom_map_upperRamificationGroupInfinite_tower`: under the same hypotheses, restriction maps the upper group of `Ω/K` onto that of `M/K`.

The proofs pass to the image of `M` in `Ω` and use the intermediate-field statements.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Infinite/ScalarTower.lean` (SHA-256 of the source file `5afccb69ebdfda35a589ca5ac51545d4ef1228868f25528de1008b856b9259ab`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
- The theorem `AlgEquiv.restrictNormal_restrictScalars` of the source is called `AlgEquiv.restrictNormal_restrictScalars_comm` here, because another library uses the source's full name for a different statement. Its statement and proof are unchanged.
