# Smoothness from the closed fibre and residue fields

Module `StacksFrontier.AlgebraicGeometry.SmoothAtClosedFibre.SeparableResidue`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file derives smoothness at x (`InfinitesimalLifting.SmoothAt`, smoothness near x) from a formally smooth local ring of the fibre, with a residue-field criterion where that ring is κ(x).

- `Stacks.SmoothAtClosedFibre.smoothAt_of_flat_of_formallySmooth_kappaToFibreStalk`: if f is locally of finite presentation, its stalk map at x flat and the fibre stalk formally smooth over κ(f(x)), then f is smooth at x.
- `residueFieldIsoFibreStalk` identifies the fibre stalk with κ(x) when the extended maximal ideal of the base stalk equals the maximal ideal at x. `kappaToFibreStalk_eq_residueFieldMap_comp` identifies the field action under this isomorphism.
- `smoothAt_of_flat_of_formallySmooth_residueFieldMap` uses that ideal equality `hm`, flatness and formal smoothness `hres` of κ(f(x)) → κ(x) to conclude smoothness at x, again for f locally of finite presentation.

The proofs transport the algebra structure of the fibre stalk along the comparison isomorphisms and conclude with `condition2_imp_condition1`.

The module docstring also lists a generic-point criterion that the file does not contain.

References include Tags 01V9, 00TV and 09E7, EGA IV 17.5.1 and SGA 3 XV 1.1.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 XV 1.1 | `smoothAt_of_flat_of_formallySmooth_kappaToFibreStalk` | partial |
| EGA | IV 17.5.1 | `smoothAt_of_flat_of_formallySmooth_residueFieldMap` | b ⇒ a when m_{Y |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/SmoothAtClosedFibre/SeparableResidue.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 5 are kept. The 2 left out are not needed by the results for which the extract is made: `Stacks.SmoothAtClosedFibre.flat_of_isField_source`, `Stacks.SmoothAtClosedFibre.smoothAt_of_mem_genericPoints_of_formallySmooth_residueFieldMap`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
