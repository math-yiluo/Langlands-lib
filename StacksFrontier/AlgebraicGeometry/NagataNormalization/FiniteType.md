# Nagata schemes under locally finite type maps

Module `StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The Nagata property passes from the base to the source of a locally finite type morphism.

`AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType` gives `IsNagataScheme X` for `f : X ⟶ S` locally of finite type with `S` Nagata.

The proof chooses a Nagata affine open near each image point and an affine neighbourhood of the source point over it. The induced map of sections is of finite type, so the ring-level Nagata theorem `isNagataRing_tfae` applies.

The module docstring also announces the spectrum of a field and schemes locally of finite type over a field; those results are not in this file.

The result is the Nagata case of Tag 035A. A further reference is EGA IV 7.7.2.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [035A](https://stacks.math.columbia.edu/tag/035A) | `isNagataScheme_of_locallyOfFiniteType` | nagata |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 7.7.2 | `isNagataScheme_of_locallyOfFiniteType` | finite type stability |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/NagataNormalization/FiniteType.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 3 declarations of the source file 1 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType_over_field`, `AlgebraicGeometry.isNagataScheme_spec_of_field`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
