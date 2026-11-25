# The normalization morphism over a normal open

Module `StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over an open subscheme that is normal, the normalization morphism of a scheme is an isomorphism.

In `AlgebraicGeometry.Scheme`, `isIso_normalization_restrict_of_isNormalRing` proves that the normalization `X.stacksNormalization hX` of a reduced scheme `X` restricts to an isomorphism over an affine open with a normal section ring. The theorem `isIso_normalization_restrict_of_isNormal` gives the same over any open `W` that is a normal scheme, including in an ambient scheme with nilpotents.

On an affine normal open, the inclusion into the integral closure in the total fraction ring is bijective. The general argument uses locality of isomorphisms on the target, first for a reduced ambient scheme, and then invariance of normalization under reduction: the closed immersion of the reduction is surjective, hence an isomorphism over the reduced open `W`.

Both results take the hypothesis `hX` that each quasi-compact open has finitely many irreducible components, which is needed to form the normalization.

The module docstring also announces a lift of a normal open into the normalization, the Japanese condition for Nagata schemes and a normal proper model of a proper variety; they are not in this file.

See Tag 034M for the normal-ring criterion and Tag 035O for reduction.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/NormalProperModel/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 4 are kept. The 6 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Scheme.exists_isOpenImmersion_normalization_of_isNormal`, `AlgebraicGeometry.exists_normal_properVariety_model`, `AlgebraicGeometry.finite_irreducibleComponents_of_isIntegral`, `AlgebraicGeometry.isFinite_normalization_of_isVariety`, `AlgebraicGeometry.isJapaneseScheme_of_isNagataScheme`, `AlgebraicGeometry.isJapaneseScheme_of_isVariety`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
