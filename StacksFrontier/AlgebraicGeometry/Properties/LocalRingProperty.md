# Local ring properties on schemes

Module `StacksFrontier.AlgebraicGeometry.Properties.LocalRingProperty`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file defines local properties of rings and what it means for a scheme to satisfy a ring property locally.

## Definitions

- `CommRing.PropertyIsLocal P` requires that P survive localization away from any one element (field `localizationAwayPreserves`) and descend from a finite family of such localizations when the elements generate the unit ideal (field `ofLocalizationSpan`). Preservation is stated for any model of the localization, while descent uses the canonical `Localization.Away` rings.
- `AlgebraicGeometry.IsLocally P X` says that every point of X has an affine open neighbourhood whose section ring satisfies P. It is an abbreviation, so its pointwise form can be used directly.

`PropertyIsLocal` here is StacksFrontier’s predicate on properties of rings in one universe, not Mathlib’s `RingHom.PropertyIsLocal` on properties of ring maps.

The module docstring also announces that finite type over ℤ, the Noetherian Cohen–Macaulay condition and the Noetherian regular condition are local, and a criterion for reducedness; none of these is in this file.

The definitions correspond to Stacks Project Tag 01OP and Tag 01OQ.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01OP](https://stacks.math.columbia.edu/tag/01OP) | `PropertyIsLocal` |  |
| [01OQ](https://stacks.math.columbia.edu/tag/01OQ) | `IsLocally` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Properties/LocalRingProperty.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 5 are kept. The 9 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isReduced_iff_isLocally_isReduced`, `CommRing.exists_away_prime_ringEquiv`, `CommRing.finiteType_int_isLocal`, `CommRing.finiteType_int_transfer_algebra`, `CommRing.isCohenMacaulayLocalRingPropForm_iff_of_ringEquiv`, `CommRing.isNoetherianCohenMacaulayRing_propertyIsLocal`, `CommRing.isRegularRing_propertyIsLocal`, `CommRing.localRingDepth_eq_of_ringEquiv`, `CommRing.localRingDepth_le_of_ringEquiv`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
