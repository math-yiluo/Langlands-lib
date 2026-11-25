# Detecting relative flatness by flat pullback

Module `StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let f : X ⟶ Y and q : Y ⟶ S be morphisms of schemes and G an arbitrary sheaf of modules on Y. Pullback along f, at a point where f is flat, both preserves and detects flatness over S at corresponding points.

`isFlatOverAt_iff_modulePullback_isFlatOverAt` assumes that f is flat at x and equates flatness over S of G at f(x) with that of its pullback at x. The structure map upstairs is the composite with q.

The pulled-back stalk is obtained by extension of scalars along the stalk map of f. A flat local map is faithfully flat, so the tensor product detects flatness over the stalk of S. The module docstring also announces the global equivalence along a surjective flat morphism, which is not in the file.

Reference is Stacks Project Tag 02JZ, for the pointwise equivalence.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02JZ](https://stacks.math.columbia.edu/tag/02JZ) | `isFlatOverAt_iff_modulePullback_isFlatOverAt` | pointwise equivalence |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/FlatMorphisms/PullbackFlatness.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isFlatOver_iff_modulePullback_isFlatOver`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
