# Local dimension from irreducible components

Module `StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

At a point of a scheme locally of finite type over a field, the local topological Krull dimension is the largest dimension of an irreducible component containing that point.

`AlgebraicGeometry.topologicalKrullDimAt_eq_iSup_irreducibleComponents` gives the supremum over the components through the point, and `exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt` proves that a component attains it. Under `Equidimensional X`, `topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional` equates local and global dimension at every point. `topologicalKrullDimAt_eq_of_equidimensional` specializes this to a specified natural-number dimension.

The proof passes to an affine neighbourhood, uses the local dimension formula in terms of components of the prime spectrum, and attains the supremum using Noetherianity there. To compare with components of X, it equips each component with its reduced closed subscheme structure and uses invariance of dimension on a nonempty open of that irreducible scheme.

The dimensions are valued in `WithBot ℕ∞`. The supremum and attainment results express the component clause of Tag 0A21. EGA IV 10.6.3 is cited for attainment and for the equidimensional case.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0A21](https://stacks.math.columbia.edu/tag/0A21) | `topologicalKrullDimAt_eq_iSup_irreducibleComponents` | local_dimension_components |
| [0A21](https://stacks.math.columbia.edu/tag/0A21) | `exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt` | local_dimension_components |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 10.6.3 | `exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt` | sup_i dim(Y_i) |
| EGA | IV 10.6.3 | `topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Variety/Defs/Dimension/Components.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
