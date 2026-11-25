# Krull dimension of a space and at a point

Module `StacksFrontier.Topology.Dimension.Krull`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The Krull dimension of a space is the supremum of the lengths of chains of irreducible closed subsets. Its dimension at a point is the least dimension of an open neighbourhood of that point.

Mathlib supplies `LTSeries` on `TopologicalSpace.IrreducibleCloseds` for chains, `RelSeries.length` for their lengths, and `topologicalKrullDim` for the supremum. The theorem `topologicalKrullDim_eq_bot_iff_isEmpty` identifies the bottom value −∞ exactly with emptiness. In a nonempty space, the closure of a point gives an irreducible closed subset.

`stacksTopologicalKrullDimAt X x` takes the infimum of `topologicalKrullDim U` over open neighbourhoods U of x, in `WithBot ℕ∞`. The theorem `topologicalKrullDimAt_isLeast` uses well-foundedness of the value type to prove that the infimum is attained. The whole space is a neighbourhood, so `topologicalKrullDimAt_le_topologicalKrullDim` bounds the pointwise dimension by the ambient one. Nonemptiness of each neighbourhood gives nonnegativity, `topologicalKrullDimAt_nonneg`. The lemmas about the definition are named with the prefix `topologicalKrullDimAt_`.

For an open embedding f, `Topology.IsOpenEmbedding.topologicalKrullDimAt_eq` equates the dimensions at x and at f x. One inequality, the private `topologicalKrullDimAt_le_of_isEmbedding_aux`, holds for any embedding and pulls back neighbourhoods; the other maps open neighbourhoods forward. This yields the homeomorphism formula `topologicalKrullDimAt_eq_of_homeomorph`. The subspace lemma `topologicalKrullDim_le_of_subset` gives monotonicity of the dimension of a subspace under inclusion of subsets.

The declarations for Tag 0055 supply the empty-space clause of part (3) and the pointwise minimum of part (4). The preceding chain notions and the ambient supremum use the existing Mathlib definitions.

EGA 0 14.1.2 and 14.1.4. SGA 3 VIB 1.5 and SGA 7 XV 1.2.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0055](https://stacks.math.columbia.edu/tag/0055) | `topologicalKrullDim_eq_bot_iff_isEmpty` | (3) |
| [0055](https://stacks.math.columbia.edu/tag/0055) | `stacksTopologicalKrullDimAt` | (4) |
| [0055](https://stacks.math.columbia.edu/tag/0055) | `topologicalKrullDimAt_isLeast` | (4) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 14.1.2 | `stacksTopologicalKrullDimAt` | dim_x formula |
| SGA | 3 VIB 1.5 | `stacksTopologicalKrullDimAt` |  |
| SGA | 7 XV 1.2 | `stacksTopologicalKrullDimAt` |  |
| EGA | 0 14.1.2 | `topologicalKrullDimAt_isLeast` | dim_x(X)=inf_U dim(U) |
| SGA | 3 VIB 1.5 | `topologicalKrullDimAt_isLeast` | partial |
| EGA | 0 14.1.4 | `topologicalKrullDim_le_of_subset` | more general |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Dimension/Krull.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 10 are kept. The 4 left out are not needed by the results for which the extract is made: `topologicalKrullDimAt_le_of_isEmbedding`, `topologicalKrullDimAt_ne_bot`, `topologicalKrullDim_eq_zero_of_discreteTopology_nonempty`, `topologicalKrullDim_preimage_val`.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `topologicalKrullDimAt` is `stacksTopologicalKrullDimAt` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 6 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
