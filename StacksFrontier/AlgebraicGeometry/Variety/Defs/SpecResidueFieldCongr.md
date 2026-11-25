# Transporting residue fields on the spectrum of a field

Module `StacksFrontier.AlgebraicGeometry.Variety.Defs.SpecResidueFieldCongr`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a field k, the canonical identifications of k with the residue fields of Spec k agree under transport along an equality of points.

`AlgebraicGeometry.spec_residueFieldEquiv_congr` takes points x and y of Spec k, their prime ideal instances, an equality h : x = y, and z ∈ k. Sending z to κ(x) and then applying `Scheme.residueFieldCongr h` gives the same element as sending z directly to κ(y). The identifications use `Ideal.algEquivResidueFieldOfField` and `Scheme.Spec.residueFieldIso`. The proof reduces to reflexivity by substituting along h.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Variety/Defs/SpecResidueFieldCongr.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
