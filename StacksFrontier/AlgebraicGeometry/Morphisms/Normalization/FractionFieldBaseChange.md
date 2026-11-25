# Normalization of the generic fibre

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FractionFieldBaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For q : W ⟶ Spec B and a fraction field L of B, normalization commutes with passage to the generic fibre, assuming every quasi-compact open of W has finitely many irreducible components.

`isPullback_normalizationSchemeMap_specMap_fractionRing` proves the cartesian normalization square for the projection from the generic fibre to W. The fraction field is supplied by a field L with `IsFractionRing B L`. `finite_irreducibleComponents_pullbackFst_fractionRing` transfers the finiteness condition to the generic fibre.

The fraction-field spectrum map is a flat preimmersion by localization, as recorded in `flat_specMap_algebraMap_fractionRing` and `isPreimmersion_specMap_algebraMap_fractionRing`. The general comparison for flat preimmersions requires a normal pulled-back normalization. Here `isNormal_pullback_normalization_pullbackFst_fractionRing` proves that hypothesis by identifying the scheme with the base change of the normalized W to Spec L.

This is the fraction-field case of Stacks Project Tag 0307 used for Tag 09IL. The file also cites Tag 07TD.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/FractionFieldBaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
