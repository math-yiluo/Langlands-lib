# Equidimensional topological spaces

Module `StacksFrontier.Topology.Dimension.Equidimensional`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Equidimensionality means that all irreducible components have the same Krull dimension as subspaces of the ambient space.

`TopologicalSpace.Equidimensional` requires pairwise equality of `topologicalKrullDim` for irreducible components. The theorem `TopologicalSpace.Equidimensional.of_preirreducibleSpace` holds because any irreducible component of a preirreducible space is the whole space. The theorem `TopologicalSpace.Equidimensional.of_homeomorph` transports the property along a homeomorphism, which takes irreducible components to irreducible components and preserves their subspace dimensions.

The definition uses pairwise equality, so it is vacuous when there are no components. The module docstring also lists the same statement for a preirreducible subset, which the file does not contain.

Stacks Project, Tag 0058. EGA 0 14.1.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0058](https://stacks.math.columbia.edu/tag/0058) | `TopologicalSpace.Equidimensional` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 14.1.3 | `TopologicalSpace.Equidimensional` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Dimension/Equidimensional.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 3 are kept. The 1 left out are not needed by the results for which the extract is made: `IsPreirreducible.equidimensional`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
