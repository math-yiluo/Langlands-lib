# Local ring properties on affine open subschemes

Module `StacksFrontier.AlgebraicGeometry.NagataNormalization.LocalProperty`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A ring property can be imposed on schemes by asking for an affine witness around each point (`AlgebraicGeometry.IsLocally`). For a local property this gives the property on every affine open; the file applies this to Nagata schemes.

`AlgebraicGeometry.IsLocally.forall_affineOpens` says that when `P` satisfies `CommRing.PropertyIsLocal` and `IsLocally P X` holds, the ring of sections of every affine open of `X` satisfies `P`. `CommRing.PropertyIsLocal.of_ringEquiv` transports such a property along a ring isomorphism. `CommRing.isNagataRing_propertyIsLocal` shows that `StacksIsNagataRing` is local, and `IsNagataScheme.isNagataRing_sections` concludes that every affine open of a Nagata scheme has a Nagata ring of sections.

The proof is the affine communication lemma, using stability under principal localization and descent from a principal cover defined by elements generating the unit ideal. Invariance under ring isomorphism views an isomorphism as localization at 1; it also transports the property between localization models.

The module docstring also announces equivalent reformulations, inheritance by open subschemes and the universally Japanese case; they are not in this file.

References are Tag 01OR for the scheme criterion, and Tag 032U and Tag 032V for the Nagata ring property.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/NagataNormalization/LocalProperty.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 15 declarations of the source file 5 are kept. The 10 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isLocally_iff_exists_affineOpenCover`, `AlgebraicGeometry.isLocally_iff_exists_openCover`, `AlgebraicGeometry.isLocally_iff_forall_affineOpens`, `AlgebraicGeometry.isLocally_open`, `CommRing.isUniversallyJapaneseRing_propertyIsLocal`, `isNagataScheme_iff_isLocally`, `isNagataScheme_open`, `isNagataScheme_tfae`, `isUniversallyJapaneseScheme_open`, `isUniversallyJapaneseScheme_tfae`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
