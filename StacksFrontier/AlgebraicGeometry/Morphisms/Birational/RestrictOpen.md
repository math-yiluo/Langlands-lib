# Open embeddings and generic points of irreducible components

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Birational.RestrictOpen`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

An open embedding of topological spaces preserves and reflects the generic points of irreducible components (the set `genericPoints`). No hypothesis on the spaces is needed.

- `Topology.IsOpenEmbedding.mem_genericPoints`: if `i : X → Y` is an open embedding and `x ∈ genericPoints X`, then `i x ∈ genericPoints Y`. The component `D` of `Y` containing the closure of `i x` pulls back to a component of `X` containing, hence equal to, the closure of `x`, and the closure of the image of that preimage is `D`.
- `Topology.IsOpenEmbedding.mem_genericPoints_of_image`: conversely, if `i x ∈ genericPoints Y`, then `x ∈ genericPoints X`, the preimage of the closure of `i x` being an irreducible component of `X`.

The module docstring speaks of birational morphisms restricted over an open and of the normalization morphism, and lists results on them; the file contains none of these, only the two lemmas above. It cites Tags 01RO, 0BXC and 0C1R.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Birational/RestrictOpen.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 2 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Scheme.isBirational_normalization_morphismRestrict`, `Topology.IsOpenEmbedding.mem_genericPoints_iff`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
