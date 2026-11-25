# The structure sheaf is of finite type

Module `StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file shows that the structure sheaf of a scheme `X`, as a module over itself, is free on one generator and of finite type.

- `structureSheafFreeIso X` (an abbreviation): the isomorphism between the free sheaf of modules on `PUnit` and the unit module `SheafOfModules.unit X.ringCatSheaf`, from `Limits.coproductUniqueIso`. Instances record that its forward morphism is an isomorphism and an epimorphism.
- `structureSheafGenerators X` (an abbreviation): the single generating section of the structure sheaf obtained from it; an instance records that it is of finite type.
- `structureSheaf_isFiniteType`: the structure sheaf is of finite type (`IsFiniteType`), with the local generators data of this one generating section.

## To watch for

- The module docstring announces the definitions of purity of a module along a fibre, universal purity and their relative and scheme versions (Tag 05J4, parts (1) to (6)). The file holds none of these; the result above is the one the docstring lists as needed to apply them to the structure sheaf. Quasi-coherence of the structure sheaf, the other property, is the library's `Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit`, proved elsewhere.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Flatness/PureModules/Purity.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 13 declarations of the source file 6 are kept. The 7 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.IsPureAlong`, `AlgebraicGeometry.IsPureRelative`, `AlgebraicGeometry.IsSchemePureAlong`, `AlgebraicGeometry.IsSchemePureRelative`, `AlgebraicGeometry.IsUniversallyPureAlong`, `AlgebraicGeometry.IsUniversallyPureRelative`, `AlgebraicGeometry.PrePureSituation.atPoint`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
