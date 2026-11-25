# Residue-field maps on affine schemes

Module `StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file compares the scheme-theoretic residue-field map of a map on spectra with the algebraic residue-field map attached to the underlying ring homomorphism.

The instance `AlgebraicGeometry.specPoint_asIdeal_isPrime` records that the ideal of a point of `Spec R` is prime, so that `Ideal.ResidueField` can be applied to it.

For a commutative ring map `f : R ⟶ T` and a point `z` of `Spec T`, `AlgebraicGeometry.specResidueFieldMap_bridge` identifies the map from the residue field at the contraction of `z` to the residue field at `z` with `Ideal.ResidueField.map` of `f`, after transport through Mathlib’s `Scheme.Spec.residueFieldIso` on both sides.

The comparison uses naturality of the map from the spectrum of a residue field, injectivity of `Spec.map`, and extensionality for algebraic residue-field maps.

The module docstring also announces transfers of `IsIso` across this identification, a composition law and a cancellation result; they are not in this file.

References are Tag 0CN7 and Tag 0CN8.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/UniversalHomeomorphism/Affine/ResidueField.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 2 are kept. The 7 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.idealResidueFieldMap_comp`, `AlgebraicGeometry.idealResidueFieldMap_id_isIso`, `AlgebraicGeometry.idealResidueFieldMap_isIso_of_specMap`, `AlgebraicGeometry.isIso_conj_residueFieldMap_iff`, `AlgebraicGeometry.isIso_left_of_isIso_comp`, `AlgebraicGeometry.isIso_residueFieldMap_of_isIso_comp`, `AlgebraicGeometry.specResidueFieldMap_isIso_of_idealResidueFieldMap`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
