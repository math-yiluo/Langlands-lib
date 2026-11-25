# Openness of the Cohen–Macaulay locus

Module `StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocusOpen`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a flat morphism locally of finite presentation, the Cohen–Macaulay condition on the local rings of the fibres defines an open subset of the source.

`isOpen_setOf_isCohenMacaulayAt` proves openness of the locus defined by `Scheme.Hom.IsCohenMacaulayAt`. It obtains the locally Noetherian fibre witnesses required by that predicate from local finite presentation.

The proof chooses affine neighbourhoods of a point and its image. On an affine chart Spec T ⟶ Spec R, with q a prime of T over p in R, it uses `affineFiber_cm_iff` and `affineFiberPoint_cm_iff_ring_locus` to test the condition on the local fibre ring T_q/pT_q. The openness half of `Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_dense_fiber` then applies. Comparisons under open immersions of source and target and under isomorphisms of arrows identify the affine locus with the restriction of the original locus.

This is the openness part of Tag 045U. The references are EGA IV 12.1.7(iii) in the flat case and EGA IV 6.11.3 in a special case.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [045U](https://stacks.math.columbia.edu/tag/045U) | `isOpen_setOf_isCohenMacaulayAt` | cm_locus_open |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 12.1.7 | `isOpen_affine_cm_locus` | (iii), special case |
| EGA | IV 12.1.7 | `isOpen_affine_scheme_cm_locus` | (iii), special case |
| EGA | IV 6.11.3 | `isOpen_affine_scheme_cm_locus` | special case |
| EGA | IV 12.1.7 | `isOpen_setOf_isCohenMacaulayAt` | (iii), flat case |
| EGA | IV 6.11.3 | `isOpen_setOf_isCohenMacaulayAt` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/LocusOpen.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
