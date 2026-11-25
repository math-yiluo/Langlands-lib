# Topological Krull dimension at a point

Module `StacksFrontier.Topology.Dimension.LocalKrullDim`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The Krull dimension of a topological space is the supremum of its dimensions at its points, where the pointwise dimension is computed using open neighbourhoods.

`TopologicalSpace.localKrullDim` is the infimum in `WithBot ℕ∞` of the Krull dimensions of open neighbourhoods of a point. The theorem `topologicalKrullDimAt_eq_localKrullDim` identifies this iterated infimum with the subtype-indexed `stacksTopologicalKrullDimAt` of `StacksFrontier.Topology.Dimension.Krull`.

For any topological space, `TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim` identifies the ambient dimension with the supremum over all points. For each chain of irreducible closed sets, take a point of its bottom member. The lemma `length_le_topologicalKrullDim_of_mem` bounds the chain's length by the dimension of every open neighbourhood of that point, restricting the chain to the neighbourhood with the same length. Each larger irreducible member meets both the neighbourhood and the complement of the preceding member, so it meets their intersection and the trace inclusion is strict. The reverse inequality uses the whole space as a neighbourhood. In the empty case both sides are −∞.

The docstrings write the name of `stacksTopologicalKrullDimAt` without its prefix `stacks`. The second module docstring describes a dimension of schemes at a point, computed from stalks, which the file does not define.

Stacks Project, Tag 0B7I and Tag 0055 (4) for the topological invariant. EGA 0 14.1.2 and 14.1.6.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0B7I](https://stacks.math.columbia.edu/tag/0B7I) | `topologicalKrullDim_eq_iSup_localKrullDim` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 14.1.2 | `localKrullDim` |  |
| EGA | 0 14.1.6 | `topologicalKrullDim_eq_iSup_localKrullDim` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Dimension/LocalKrullDim.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 5 are kept. The 3 left out are not needed by the results for which the extract is made: `Scheme.localKrullDim`, `Scheme.localKrullDim_specClosedPoint`, `specClosedPoint`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
