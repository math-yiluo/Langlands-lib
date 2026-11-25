# Finite base change of upper ramification inside a Galois extension

Module `FontaineWintenberger.APF.BaseChange.Infinite`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file has one theorem. Let `K` be a complete discretely valued field with perfect residue field (`IsPerfectResidueLocalField K`), `C` a finite separable extension of `K`, itself a complete discretely valued normed field with perfect residue field, and `M` a Galois extension of `K` containing `C`.

`mem_upperRamificationGroupInfinite_finiteBase_tower_iff`: for `u ≥ -1` and `σ` in `Gal(M/C)`, `σ` lies in the upper ramification group of `M/C` with parameter `v = apfPsi K C u` if and only if `σ`, seen as a `K`-automorphism, lies in the upper ramification group of `M/K` with parameter `u`. In short, `Gal(M/C)^v = Gal(M/C) ∩ Gal(M/K)^u`.

The proof lifts automorphisms to `SeparableClosure K`, applies the statement for the separable closure (`AbstractFiniteBase.mem_upper_finiteBase_iff`), and restricts back to `M`; lifting and restriction of upper groups in a tower come from the module on scalar towers of infinite ramification, together with `AlgEquiv.restrictNormal_restrictScalars_comm`.

To watch for: `M` and `C` come with fixed algebra structures to `SeparableClosure K`, compatible in towers, as instance arguments. The upper groups are the library's `upperRamificationGroupInfinite`, for possibly infinite extensions.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/BaseChange/Infinite.lean` (SHA-256 of the source file `9a684719afc9290d525ed072a170b47e58b72b880319d76bfe18e0c5e46ce0e0`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
- The proof cites `AlgEquiv.restrictNormal_restrictScalars_comm` (module `FontaineWintenberger.Ramification.Infinite.ScalarTower`), which the source calls `AlgEquiv.restrictNormal_restrictScalars`; the theorem was renamed because another library uses that full name for a different statement. The proof is otherwise unchanged.
