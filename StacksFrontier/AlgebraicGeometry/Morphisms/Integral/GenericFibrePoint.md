# Generic fibre points under integral composition

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Integral.GenericFibrePoint`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Composing a scheme morphism with an integral map of bases preserves the property of being the generic point of an irreducible component of a fibre.

`eq_of_specializes_of_base_eq_of_isIntegralHom` proves that two comparable points in a fibre of an integral morphism i : T ⟶ S are equal. Given g : X ⟶ T and i integral, `mem_genericPoints_asFiber_comp_of_isIntegralHom` takes a point x generic in an irreducible component of its g-fibre and gives the same property in its fibre for the composite.

The proof uses the closedness of points in integral fibres. A generalization of x in the composite fibre must have the same image under g as x, so genericity in the g-fibre forces equality.

References are Stacks Project Tag 02NT for the integral-fibre lemma and Tag 09IL for the reduced-fibre application.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Integral/GenericFibrePoint.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
