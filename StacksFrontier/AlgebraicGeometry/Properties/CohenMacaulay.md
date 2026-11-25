# Cohen–Macaulay schemes

Module `StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The definition `AlgebraicGeometry.IsCohenMacaulay` says that every point of a scheme X has an affine open neighborhood U whose section ring Γ(X, U) is Noetherian and Cohen–Macaulay.

The simp lemma `isCohenMacaulay_iff` exposes this condition directly. The module docstring also announces a lemma extracting the neighborhood at a point and the case of a scheme with no points; neither is in this file.

Noetherianity of the neighborhood’s ring is included as a witness in the definition because `IsCohenMacaulayRing` takes it as a typeclass argument.

References are Stacks Project Tag 02IO for schemes and Tag 00NC for rings, and EGA IV 5.7.1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02IO](https://stacks.math.columbia.edu/tag/02IO) | `IsCohenMacaulay` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 5.7.1 | `IsCohenMacaulay` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Properties/CohenMacaulay.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 2 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.IsCohenMacaulay.exists_affineOpen`, `AlgebraicGeometry.isCohenMacaulay_of_isEmpty`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
