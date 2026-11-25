# Generic points of a scheme and the specialization order

Module `StacksFrontier.AlgebraicGeometry.Properties.Dimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file characterizes the generic points of the irreducible components of a scheme by the specialization order.

For any scheme X, `mem_genericPoints_iff_isMax` says that a point x is the generic point of an irreducible component exactly when it is maximal for the specialization order, that is, when it has no proper generalization. The proof compares the closure of x with an irreducible component containing it and with the generic point of that component.

The module docstring also announces results relating the dimension of a scheme to its local rings, the decomposition of a locally Noetherian scheme of dimension at most zero, and the characterization of isolated points; they are not in this file. It calls the dimension at a point `topologicalKrullDimAt`, a notion declared elsewhere as `stacksTopologicalKrullDimAt`.

The tables list Tag 04MT and EGA 0 14.1.2 for the dimension of a scheme and at a point, and Tag 04MU for the topological supremum formulas; these notions are declared in other files.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [04MT](https://stacks.math.columbia.edu/tag/04MT) | `topologicalKrullDim` | dimension of a scheme |
| [04MT](https://stacks.math.columbia.edu/tag/04MT) | `stacksTopologicalKrullDimAt` | dimension of a scheme at a point |
| [04MU](https://stacks.math.columbia.edu/tag/04MU) | `TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim` | dimension_sup_at_points |
| [04MU](https://stacks.math.columbia.edu/tag/04MU) | `TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim` | dimension_sup_at_points |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 14.1.2 | `topologicalKrullDim` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Properties/Dimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 1 are kept. The 7 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isArtinianRing_stalk_of_topologicalKrullDim_le_zero`, `AlgebraicGeometry.isIso_sigmaFromSpecStalk_of_topologicalKrullDim_le_zero`, `AlgebraicGeometry.ringKrullDim_stalk_eq_zero_iff_mem_genericPoints`, `AlgebraicGeometry.sigmaFromSpecStalk`, `AlgebraicGeometry.topologicalKrullDimAt_eq_zero_iff_isIsolatedPoint`, `AlgebraicGeometry.topologicalKrullDimAt_eq_zero_of_isOpen_singleton`, `AlgebraicGeometry.topologicalKrullDim_eq_iSup_krullDimOfRing_stalk`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
