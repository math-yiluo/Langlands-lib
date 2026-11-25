# Separability for arbitrary field extensions

Module `StacksFrontier.FieldTheory.Separable.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file defines separability for field extensions K/k that may be transcendental, by testing finitely generated intermediate extensions.

The library's class `Algebra.StacksIsSeparableExtension k K` requires every intermediate field L finitely generated over k to be separably generated. Its projection `Algebra.StacksIsSeparableExtension.isSeparablyGenerated` is declared an instance.

The definition uses Mathlib's `Algebra.IsSeparablyGenerated`, which asks for a subset s forming a transcendence basis such that K is separable algebraic over k(s). Finite generation of L as a field is expressed by `Algebra.EssFiniteType k L`. Mathlib's `Algebra.IsSeparable` expresses algebraic separability, which is also what these notions mean for algebraic field extensions.

The module docstring calls the class and its projection by their names without the prefix `Stacks`.

The references are Tag 030O, part (2), and SGA 1 II 5.6.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [030O](https://stacks.math.columbia.edu/tag/030O) | `StacksIsSeparableExtension` | part (2) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 1 II 5.6 | `StacksIsSeparableExtension` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/FieldTheory/Separable/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 3 are kept. The 1 left out are not needed by the results for which the extract is made: `Algebra.isSeparableExtension_iff`.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `Algebra.IsSeparableExtension` is `Algebra.StacksIsSeparableExtension` here; `Algebra.IsSeparableExtension.isSeparablyGenerated` is `Algebra.StacksIsSeparableExtension.isSeparablyGenerated` here; `Algebra.IsSeparableExtension.mk` is `Algebra.StacksIsSeparableExtension.mk` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
