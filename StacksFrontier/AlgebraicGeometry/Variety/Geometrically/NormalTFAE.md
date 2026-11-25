# Normality of a scheme through its local rings

Module `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves two lemmas on normal schemes. `IsNormal` is this library's class (from `StacksFrontier.AlgebraicGeometry.Properties.Normal`): every local ring is an integrally closed domain.

- `AlgebraicGeometry.isNormal_iff_stalk_isNormalRing` says that a scheme Y is normal exactly when each of its local rings satisfies Mathlib's `IsNormalRing`. A local ring is a normal ring exactly when it is an integrally closed domain, so this restates `isNormal_iff_stalk_normal`.
- `isNormal_of_iso` transports normality along an isomorphism of schemes Y ≅ Z, using the isomorphisms it induces on local rings.

The module docstring describes the characterizations of geometrically normal schemes over a field (Tag 038O) and the identification of base changes of affine opens used to prove them; none of these is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Variety/Geometrically/NormalTFAE.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 2 are kept. The 6 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.affineBaseChangeIso`, `AlgebraicGeometry.geometricallyNormal_tfae`, `AlgebraicGeometry.isGeometricallyNormal_of_finitePurelyInseparable`, `AlgebraicGeometry.isGeometricallyNormal_of_perfectClosure`, `AlgebraicGeometry.isNormal_pullback_iff_affineSections`, `AlgebraicGeometry.isNormal_spec_iff`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
