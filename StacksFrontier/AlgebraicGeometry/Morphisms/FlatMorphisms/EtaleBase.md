# Relative flatness over an étale intermediate base

Module `StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let f : X ⟶ T and g : T ⟶ S be morphisms of schemes with g étale, and let F be a quasi-coherent module on X. Flatness over S and flatness over T then give equivalent conditions on F.

`isFlatOverAt_comp_iff_of_etale` compares flatness of F at a given point of X over the two local rings at its images. `isFlatOver_comp_iff_of_etale` gives the equivalence at all points. Both use the relative flatness predicates for the underlying ringed spaces.

To pass from S to T, the proof first pulls F back to X ×ₛ T and uses preservation of relative flatness by base change. The graph of f into this product is an open immersion because it is obtained from the diagonal of the unramified map g by pullback. Restriction to the graph recovers F and its flatness over T. The implication from T to S uses `IsFlatOverAt.comp` and flatness of g.

Reference is Stacks Project Tag 05B9.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [05B9](https://stacks.math.columbia.edu/tag/05B9) | `isFlatOverAt_comp_iff_of_etale` | pointwise statement |
| [05B9](https://stacks.math.columbia.edu/tag/05B9) | `isFlatOver_comp_iff_of_etale` | global statement |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/FlatMorphisms/EtaleBase.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
