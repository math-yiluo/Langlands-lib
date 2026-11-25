# Generic points under flat morphisms

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FlatCodimensionZero`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`mem_genericPoints_of_flat` proves that a flat morphism of schemes f : X ⟶ Y carries a generic point of an irreducible component of X to a generic point of an irreducible component of Y: a flat morphism is generalizing, and a generalizing map carries generic points to generic points.

This is the representable case of Stacks Project Tag 0GMC, which is the second conclusion of Tag 0GMD. The module docstring also announces the first conclusion of Tag 0GMD, with the condition of Tag 0BB1: along a flat morphism locally of finite type, finitely many irreducible components on every quasi-compact open ascends from target to source. That result is not in the file.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0GMC](https://stacks.math.columbia.edu/tag/0GMC) | `mem_genericPoints_of_flat` | representable case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/FlatCodimensionZero.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 1 are kept. The 6 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.finite_genericPoints_of_flat_locallyOfFiniteType_affine`, `AlgebraicGeometry.finite_irreducibleComponents_of_finite_genericPoints`, `AlgebraicGeometry.finite_irreducibleComponents_of_finite_open_cover`, `AlgebraicGeometry.finite_irreducibleComponents_of_flat_locallyOfFiniteType`, `AlgebraicGeometry.genericPoint_mem_fiber_of_genericPoint`, `AlgebraicGeometry.genericPoints_of_open`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The 2 references to EGA and SGA that the source writes as attributes of that library belong to declarations left out; none remains.
