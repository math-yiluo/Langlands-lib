# Unramified morphisms

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file defines unramifiedness of a scheme morphism, at a point and globally, by asking for affine neighbourhoods around each source point.

For `f : X ⟶ S` and `x ∈ X`, `AlgebraicGeometry.UnramifiedAt` asks for affine opens `U` containing `x` and `V` containing `f(x)` with `U ⊆ f⁻¹(V)`. The induced algebra of sections, given by `Scheme.Hom.appLE`, must satisfy `Algebra.Unramified`. The class `Unramified` requires this condition at every source point through its field `unramifiedAt`; its pointwise equivalence is `unramified_iff`.

These are StacksFrontier’s own notions for scheme morphisms; the condition on rings is Mathlib’s `Algebra.Unramified`, formally unramified and of finite type.

The module docstring also lists G-unramified versions of both definitions and their pointwise characterization; they are not in this file.

The two definitions correspond to parts (1) and (3) of Tag 02G4. Additional references are SGA 3 XI 1.3 and 1.5.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02G4](https://stacks.math.columbia.edu/tag/02G4) | `UnramifiedAt` | part (1) |
| [02G4](https://stacks.math.columbia.edu/tag/02G4) | `Unramified` | part (3) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 XI 1.3 | `UnramifiedAt` |  |
| SGA | 3 XI 1.5 | `UnramifiedAt` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Unramified/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 5 are kept. The 5 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.GUnramified`, `AlgebraicGeometry.GUnramified.gUnramifiedAt`, `AlgebraicGeometry.GUnramified.mk`, `AlgebraicGeometry.GUnramifiedAt`, `AlgebraicGeometry.gUnramified_iff`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
