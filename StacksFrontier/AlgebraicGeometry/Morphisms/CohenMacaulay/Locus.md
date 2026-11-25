# The Cohen–Macaulay locus in each fibre

Module `StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Locus`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a flat morphism locally of finite presentation, the Cohen–Macaulay locus is determined by the fibre local rings and is dense in every scheme-theoretic fibre.

`isCohenMacaulayAt_set_eq_fiberLocalRing` identifies the locus defined by `Scheme.Hom.IsCohenMacaulayAt` with the points x where the stalk at `f.asFiber x` is Cohen–Macaulay. Flatness supplies the stalkwise flatness in the pointwise predicate. Local finite presentation supplies local Noetherianity of the fibres.

`dense_cohenMacaulayAt_fiber` proves density of the inverse image of this locus under each fibre inclusion. In an affine neighbourhood in the fibre, a minimal prime under a given prime yields a generization with a zero-dimensional Noetherian local ring, which is Cohen–Macaulay.

Tag 045U (fibre-local-ring characterization and fibrewise density). SGA 4 XVIII 2.3 (fibrewise density).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [045U](https://stacks.math.columbia.edu/tag/045U) | `isCohenMacaulayAt_set_eq_fiberLocalRing` | fibre_local_ring_characterization |
| [045U](https://stacks.math.columbia.edu/tag/045U) | `dense_cohenMacaulayAt_fiber` | cm_locus_fibrewise_dense |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 4 XVIII 2.3 | `dense_cohenMacaulayAt_fiber` | fibrewise density |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/Locus.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
