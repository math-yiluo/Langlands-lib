# Irreducible closed subsets restricted to an open subspace

Module `StacksFrontier.Topology.Dimension.CodimensionOpen`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

An irreducible closed subset Y of X meeting an open subspace gives an irreducible closed subset of that subspace. The file works with irreducible closed subsets of arbitrary topological spaces.

In `TopologicalSpace.IrreducibleCloseds`, `comapOpenEmbedding` bundles the preimage of Y along an open embedding f from W to X as an irreducible closed subset of W, provided the preimage is nonempty: it is closed because f is continuous, and irreducible because a nonempty preimage of an irreducible set under an open embedding is again irreducible. The definition `restrictOpen` specializes this to the inclusion of an open U with Y ∩ U nonempty, the trace being nonempty by `nonempty_preimage_val_of_inter_nonempty`. The carrier of the restriction is the subset `Subtype.val ⁻¹' Y` of the subtype U, the points of U lying in Y. The simp lemmas `coe_comapOpenEmbedding` and `coe_restrictOpen` give the two carriers.

The module docstring announces the equality of the codimensions of Y in X and of Y ∩ U in U (Tag 02I4); the file does not prove it.

The restriction is EGA 0 2.1.6.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 2.1.6 | `restrictOpen` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Dimension/CodimensionOpen.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 5 are kept. The 5 left out are not needed by the results for which the extract is made: `TopologicalSpace.IrreducibleCloseds.coheight_comapOpenEmbedding`, `TopologicalSpace.IrreducibleCloseds.coheight_restrictOpen`, `TopologicalSpace.IrreducibleCloseds.image_coe_restrictOpen`, `TopologicalSpace.IrreducibleCloseds.map_comapOpenEmbedding`, `TopologicalSpace.IrreducibleCloseds.map_subtypeVal_restrictOpen`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
