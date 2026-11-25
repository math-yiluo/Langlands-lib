# Reduced structures on closed subschemes

Module `StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A closed subset of a scheme carries the closed subscheme cut out by its vanishing ideal sheaf. The file verifies that this scheme is reduced.

In `Scheme.IdealSheafData`, `isReduced_subscheme` proves reducedness when the component ideal on every affine open is radical. The instances `isReduced_subscheme_radical` and `stacks_isReduced_subscheme_vanishingIdeal` apply to radicals of ideal sheaves and to vanishing ideals of closed subsets, respectively.

The proof checks reducedness on the affine cover by spectra of quotient rings, using reducedness of quotients by radical ideals.

The contribution to Tag 01J3 is the reducedness of the induced closed subscheme.

## Watch for

- The module docstring lists the instance for vanishing ideals under its name in the source, without the prefix `stacks_`. It also announces that the subscheme is supported exactly on the closed subset, and an irreducibility criterion; the file holds neither.

The references include EGA I (5.1.2, 5.1.3, 5.2.1(b), 5.5.4), EGA II (6.5.1), EGA IV (3.4.1 and 4.9.4), SGA 3 (XV, 3.2) and SGA 6 (X, 1.1.2).

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 5.1.2 | `isReduced_subscheme_radical` | more general |
| EGA | I 5.1.2 | `stacks_isReduced_subscheme_vanishingIdeal` | reducedness |
| EGA | I 5.2.1 | `stacks_isReduced_subscheme_vanishingIdeal` | (b) reduced, closed case |
| EGA | I 5.1.3 | `stacks_isReduced_subscheme_vanishingIdeal` | more general |
| EGA | I 5.5.4 | `stacks_isReduced_subscheme_vanishingIdeal` | partial |
| EGA | II 6.5.1 | `stacks_isReduced_subscheme_vanishingIdeal` | partial |
| EGA | IV 3.4.1 | `stacks_isReduced_subscheme_vanishingIdeal` | partial |
| EGA | IV 4.9.4 | `stacks_isReduced_subscheme_vanishingIdeal` | partial |
| SGA | 3 XV 3.2 | `stacks_isReduced_subscheme_vanishingIdeal` | partial |
| SGA | 6 X 1.1.2 | `stacks_isReduced_subscheme_vanishingIdeal` | reducedness of Z(x) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Limits/ReducedInducedSubscheme.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 3 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Scheme.IdealSheafData.irreducibleSpace_subscheme`, `AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι_vanishingIdeal`.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal` is `AlgebraicGeometry.Scheme.IdealSheafData.stacks_isReduced_subscheme_vanishingIdeal` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 10 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
