# Étaleness at a smooth unramified point

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a morphism of schemes, smoothness and unramifiedness at the same source point are equivalent to étaleness there.

`etaleAt_iff_smoothAt_and_unramifiedAt` identifies `EtaleAt f x` with the conjunction of `InfinitesimalLifting.SmoothAt f x` and `UnramifiedAt f x`. This is the pointwise criterion.

`formallyUnramified_stalkMap_iff` says that, for compatible affine neighbourhoods of x and its image, the stalk map is formally unramified exactly when the corresponding prime lies in the unramified locus of the map on sections. The converse of the étale criterion uses this lemma to move the unramifiedness condition to the smooth affine chart, then shrinks to a basic open where the ring map is both smooth and formally unramified.

Tag 02GK. EGA IV 17.6.2 and SGA 3 XI 1.4 give more general results.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02GK](https://stacks.math.columbia.edu/tag/02GK) | `etaleAt_iff_smoothAt_and_unramifiedAt` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 17.6.2 | `etaleAt_iff_smoothAt_and_unramifiedAt` | more general |
| SGA | 3 XI 1.4 | `etaleAt_iff_smoothAt_and_unramifiedAt` | more general |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Etale/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
