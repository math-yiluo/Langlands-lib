# Relative flatness of modules after base change

Module `StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Pullback of a quasi-coherent module preserves flatness over the base at corresponding points. The base change S′ ⟶ S may be arbitrary.

`modulePullback_isFlatOverAt` takes a cartesian square with X′ ⟶ X over S′ ⟶ S, a quasi-coherent module F on X, and a point x′ of X′. If F is flat over S at the image of x′ in X, its pullback along X′ ⟶ X is flat over S′ at x′.

In the proof the local ring of the fibre product is a localization of the tensor product of the two local rings over the base local ring. The stalk of the pulled-back module is scalar extension to that localization, so the algebraic base-change and localization results give flatness over the new base stalk. The result is transported from the chosen fibre product to a square supplied as `IsPullback` using the pullback isomorphism and functoriality of module pullback. The module docstring also announces the global statement, for a module flat over S at all points, which is not in the file.

References are Stacks Project Tag 01U8, EGA IV 2.1.4 for the pointwise statement, and SGA 3 V 7.4(i) for base change.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01U8](https://stacks.math.columbia.edu/tag/01U8) | `modulePullback_isFlatOverAt` | flatness at a point |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 2.1.4 | `modulePullback_isFlatOverAt` | pointwise statement |
| SGA | 3 V 7.4 | `modulePullback_isFlatOverAt` | (i) base change |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/FlatMorphisms/BaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 3 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.modulePullback_isFlatOver`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
