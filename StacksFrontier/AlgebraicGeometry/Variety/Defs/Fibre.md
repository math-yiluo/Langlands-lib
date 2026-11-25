# Fibres of morphisms locally of finite type

Module `StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The fibre of a locally finite type morphism is locally of finite type over the residue field of its base point. This gives local Noetherianity.

`AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField` registers this as an instance for any f : X ⟶ Y locally of finite type and any point y of Y, using stability of local finite type under base change to Spec κ(y). No base field is involved.

`isLocallyNoetherian_fiber_of_locallyOfFiniteType` uses local Noetherianity of Spec κ(y) to show that the fibre over y is locally Noetherian.

The module docstring also announces the corresponding statement for a morphism of schemes over a field and the finiteness of the irreducible components of a fibre of a quasi-compact morphism; neither is in the file. The docstring cites Tag 0B2L, and EGA I 6.4.11 is cited for the instance (partial).

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 6.4.11 | `Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Variety/Defs/Fibre.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 2 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.finite_irreducibleComponents_fiber`, `AlgebraicGeometry.locallyOfFiniteType_fiberToSpecResidueField`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
