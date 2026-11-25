# Morphisms of finite presentation

Module `StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`AlgebraicGeometry.FinitePresentation f` says that a morphism of schemes f is of finite presentation: it is the conjunction of Mathlib’s `LocallyOfFinitePresentation f`, quasi-compactness and quasi-separatedness. It is an `abbrev` for a proposition, not a class, so it gives no instances; `FinitePresentation.locallyOfFinitePresentation` extracts the first component.

The module docstring also announces finite presentation at a point and stability under base change, which are not in the file.

Stacks Project, Tag 01TP, parts (2) and (3); the module docstring also cites Tag 01TS, for base change. EGA IV 1.4.2 and SGA 3 VIB 1.3 concern the local condition.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01TP](https://stacks.math.columbia.edu/tag/01TP) | `FinitePresentation` | part (3) |
| [01TP](https://stacks.math.columbia.edu/tag/01TP) | `AlgebraicGeometry.LocallyOfFinitePresentation` | part (2) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 VIB 1.3 | `AlgebraicGeometry.LocallyOfFinitePresentation` |  |
| EGA | IV 1.4.2 | `AlgebraicGeometry.LocallyOfFinitePresentation` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/FinitePresentationPoint.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 2 are kept. The 5 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.FinitePresentation.mk`, `AlgebraicGeometry.FinitePresentation.quasiCompact`, `AlgebraicGeometry.FinitePresentation.quasiSeparated`, `AlgebraicGeometry.FinitePresentationAt`, `AlgebraicGeometry.finitePresentation_isStableUnderBaseChange`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
