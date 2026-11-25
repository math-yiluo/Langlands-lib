# Separating transcendence bases of finitely generated subextensions

Module `StacksFrontier.FieldTheory.Separable.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A separating transcendence basis upstairs implies that each finitely generated subextension has a finite separating transcendence basis.

If K/k has a separating transcendence basis s, so that K is separable algebraic (Mathlib's `Algebra.IsSeparable`) over k(s), and L is in a tower k ⟶ L ⟶ K, `exists_isTranscendenceBasis_and_isSeparable_of_isSeparable_adjoin_of_essFiniteType` produces a finite transcendence basis t for L/k with L separable algebraic over k(t). The proof passes geometric reducedness from K to L, and a geometrically reduced finitely generated extension has a finite separating transcendence basis. The hypothesis `Algebra.EssFiniteType k L` means finite generation as a field. The theorem restates `Stacks.Separable.SeparablyGenerated.solution`.

The module docstring also announces that separability in the sense of Definition 030O (2) passes to subextensions (Tag 030P); that result is not in the file.

The references are Tag 030X for the basis result and Tag 030O for the definition.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [030X](https://stacks.math.columbia.edu/tag/030X) | `exists_isTranscendenceBasis_and_isSeparable_of_isSeparable_adjoin_of_essFiniteType` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/FieldTheory/Separable/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 3 are kept. The 2 left out are not needed by the results for which the extract is made: `Algebra.isSeparableExtension_tower_bot_of_isSeparableExtension`, `IntermediateField.isSeparableExtension_tower_bot`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
