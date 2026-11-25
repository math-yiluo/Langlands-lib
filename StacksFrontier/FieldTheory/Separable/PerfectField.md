# Separability over a perfect field

Module `StacksFrontier.FieldTheory.Separable.PerfectField`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Every extension of a perfect field is separable in the sense that each finitely generated intermediate field has a separating transcendence basis.

`Algebra.stacks_isSeparableExtension_of_perfectField` assumes a field extension K/k with k perfect. It applies Mathlib's `exists_isTranscendenceBasis_and_isSeparable_of_perfectField` to each intermediate field finitely generated over k. The conclusion is the library's `Algebra.StacksIsSeparableExtension k K`, which includes transcendental extensions. It is a lemma, not an instance.

The module docstring and the lemma's docstring use the names of the class and of the lemma without the prefix `Stacks`.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/FieldTheory/Separable/PerfectField.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `Algebra.isSeparableExtension_of_perfectField` is `Algebra.stacks_isSeparableExtension_of_perfectField` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
