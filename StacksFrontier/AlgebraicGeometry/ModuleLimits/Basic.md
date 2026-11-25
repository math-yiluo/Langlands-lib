# Inverse image of a finitely presented module on schemes

Module `StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One result on sheaves of modules on schemes.

- `Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback`: for a morphism of schemes `f : X ⟶ Y` and a module `M` of finite presentation on `Y` (an instance argument), the inverse image `(Scheme.Modules.pullback f).obj M` is of finite presentation. It is the library's result for ringed spaces, `Stacks.SheafOfModules.modulePullback_isFinitePresentation`, applied to the underlying morphism of ringed spaces.

## Watch for

- The module docstring announces that a finitely presented module on a cofiltered limit of affine schemes, or of schemes with affine transitions and an affine stage, comes by pullback from a stage (the affine case of Tag 01ZR (1)). The file holds neither statement; the variables `D`, `c` and `hc` it declares for them are not used.

## References

Tag 01BQ, which the docstring of the result names for ringed spaces.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/ModuleLimits/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 3 declarations of the source file 1 are kept. The 2 left out are not needed by the results for which the extract is made: `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_isLimit`, `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_isLimit_of_isAffine_stage`.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
