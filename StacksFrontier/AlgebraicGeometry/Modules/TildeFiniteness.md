# Finiteness of modules and their associated sheaves

Module `StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

On Spec R for a commutative ring R, finite generation and finite presentation of an R-module can be detected by the corresponding local properties of its associated sheaf.

- `AlgebraicGeometry.tilde_isFiniteType_iff` identifies finite type of the sheaf associated to M with finite generation of M over R.
- `tilde_isFinitePresentation_iff` identifies finite presentation of the associated sheaf with finite presentation of M over R.
- `tilde_has_finite_presentation` constructs a finite global sheaf presentation from a finitely presented R-module.

For finite generation, a finite standard-open refinement of local generator data gives finite generation of the localized modules, which implies finite generation of M. In the other direction, a finite generating family gives global sheaf generators via the tilde presentation. For finite presentation, choose a surjection onto M from a finite free module. The corresponding sheaf kernel is of finite type, and exactness of tilde identifies it with the sheaf of the module kernel. The finite-type equivalence then gives finitely many relations. Conversely, a finite module presentation yields a finite sheaf presentation.

Both sheaf properties are expressed through data on a cover. The equivalences concern associated sheaves `M^~`, not an arbitrary quasi-coherent sheaf on Spec R.

References include Tag 01PB and Tag 01PC. EGA II 1.4.5 is cited for finite type in the affine case with B equal to the structure sheaf.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01PB](https://stacks.math.columbia.edu/tag/01PB) | `tilde_isFiniteType_iff` |  |
| [01PC](https://stacks.math.columbia.edu/tag/01PC) | `tilde_isFinitePresentation_iff` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 1.4.5 | `tilde_isFiniteType_iff` | affine base, B = O_Y |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Modules/TildeFiniteness.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 6 declarations of the source file 5 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.finitePresentation_sections_of_affine`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
