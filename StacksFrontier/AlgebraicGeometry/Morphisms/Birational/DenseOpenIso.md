# Dense open isomorphisms from birational morphisms

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Birational.DenseOpenIso`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A birational morphism can be restricted to an isomorphism of dense opens under suitable finite type or finite presentation hypotheses.

`exists_dense_opens_isIso_resLE_of_isBirational` takes a birational f : X ⟶ Y with finitely many irreducible components on both sides. Its hypothesis `hfin` requires either that f be locally of finite type and Y reduced, or that f be locally of finite presentation. It gives dense opens U ⊆ X and V ⊆ Y such that U ⊆ f⁻¹V and the restriction U ⟶ V is an isomorphism.

At each generic point of X, a local extension theorem extends the inverse on stalks to a map from a neighbourhood in Y. Local uniqueness of maps with the same stalk map lets the proof shrink to an open immersion near that generic point. Pairwise disjoint neighbourhoods of the generic points of Y let these local open immersions combine, and their domain and image contain the generic points on the respective sides.

This file treats the dense-open-isomorphism part of Tag 0BAC. The formulation of its final assertion using dominant rational maps in the sense of Tag 0A20 is given separately by `Scheme.dominantBirationalOver_of_isBirational`. The module docstring also announces a version over a base, yielding a partial isomorphism over it; the file does not contain it.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0BAC](https://stacks.math.columbia.edu/tag/0BAC) | `exists_dense_opens_isIso_resLE_of_isBirational` | dense open isomorphism |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Birational/DenseOpenIso.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 3 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.birationalOver_of_isBirational`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
