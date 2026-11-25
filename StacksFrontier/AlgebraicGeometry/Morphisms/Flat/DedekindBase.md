# Flatness over a Dedekind domain

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Flat.DedekindBase`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Morphisms to the spectrum of a Dedekind domain are flat when the source is reduced and every irreducible component dominates the base.

`flat_of_forall_genericPoint_map_eq` proves flatness of a morphism q from a reduced scheme to Spec A, A a Dedekind domain, if every point whose closure is an irreducible component maps to the generic point of the base. The reduced source may be non-Noetherian.

Flatness is checked on stalks: the local ring of the base is a localized Dedekind domain, over which torsion-free modules are flat, so it suffices that a product of the image of a base germ a with a germ b upstairs vanishes only when a or b does. For b nonzero, `exists_genericPoint_stalkSpecializes_ne_zero` finds a component on which b survives, while `stalkSpecializes_injective_of_isIntegral` lets the proof test a nonzero base germ in the field at the generic point.

The module docstring also announces a separate result for integral sources, which is not in the file.

References are Stacks Project Tag 0AUW and Tag 0CC1, and EGA I 8.2.1 for specialization of local rings.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 8.2.1 | `stalkSpecializes_injective_of_isIntegral` | more general |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Flat/DedekindBase.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 4 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.flat_of_genericPoint_map_eq`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
