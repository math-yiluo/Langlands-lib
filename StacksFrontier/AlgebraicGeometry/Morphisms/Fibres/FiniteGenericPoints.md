# Finiteness of fibre generic points in a closed subset

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.FiniteGenericPoints`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let f be a quasi-compact, locally finite type morphism to the spectrum of a Dedekind domain. A closed subset Z that is nowhere dense in the generic fibre contains only finitely many points that are generic in an irreducible component of their own fibre.

`AlgebraicGeometry.finite_setOf_mem_genericPoints_fiber` proves this finiteness with generic-fibre nowhere density expressed by pulling Z back along the fibre inclusion. `noetherianSpace_fiber` shows that every fibre of a quasi-compact morphism locally of finite type has a Noetherian underlying space. `notMem_of_mem_genericPoints_fiber` shows that if Z contains a fibre component’s generic point then its pullback to that fibre fails to be nowhere dense.

Nowhere density persists over a nonempty open of the base by Tag 054X. The complement is a finite set of points because the base is a Dedekind spectrum. Each remaining fibre has finitely many irreducible components, so their generic points give a finite set containing all the required points.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Fibres/FiniteGenericPoints.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
