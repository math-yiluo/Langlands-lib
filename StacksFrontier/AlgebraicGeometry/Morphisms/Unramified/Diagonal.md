# Open diagonals of unramified morphisms

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The diagonal of an unramified scheme morphism is an open immersion.

For `f : X ⟶ S` with `[Unramified f]`, the instance `Unramified.isOpenImmersion_diagonal` makes `pullback.diagonal f` an open immersion. The proof reads unramifiedness as local finite type together with formal unramifiedness, by `unramified_iff_locallyOfFiniteType_and_formallyUnramified`, and then applies Mathlib’s diagonal result for formal unramifiedness.

The module docstring also announces converse statements and an étale cancellation result; they are not in this file.

The statement is part (1) of Tag 02GE. Further references are EGA IV 17.4.1 and 17.4.2, SGA 1 I 3.1 and 3.4, and SGA 3 XI 1.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02GE](https://stacks.math.columbia.edu/tag/02GE) | `isOpenImmersion_diagonal` | part (1) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 17.4.2 | `isOpenImmersion_diagonal` | a) ⇒ b) |
| SGA | 3 XI 1.3 | `isOpenImmersion_diagonal` | (a) => (b) |
| EGA | IV 17.4.1 | `isOpenImmersion_diagonal` | a) => b) |
| SGA | 1 I 3.4 | `isOpenImmersion_diagonal` | diagonal case (g = id) |
| SGA | 1 I 3.1 | `isOpenImmersion_diagonal` | (ii) => (iii) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Unramified/Diagonal.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 1 are kept. The 3 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Etale.of_comp_of_unramified`, `AlgebraicGeometry.GUnramified.of_isOpenImmersion_diagonal`, `AlgebraicGeometry.Unramified.of_isOpenImmersion_diagonal`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
