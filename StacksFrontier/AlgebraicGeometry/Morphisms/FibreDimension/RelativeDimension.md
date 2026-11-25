# Relative dimension of a scheme morphism

Module `StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file defines the exact relative dimension of a morphism locally of finite type.

`RelativeDimension f d`, for `f` with `LocallyOfFiniteType f` and d in ℕ, requires every nonempty fibre to be equidimensional and to have topological Krull dimension d, compared in `WithBot ℕ∞`. It imposes a fibrewise equidimensionality requirement and is vacuous on empty fibres. The `simp` lemma `relativeDimension_iff` unfolds the definition.

The module docstring also describes two notions of relative dimension at most d, at a point and at every point, with lemmas on them; the file does not contain them.

Stacks Project, Tag 02NJ, part (3).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02NJ](https://stacks.math.columbia.edu/tag/02NJ) | `RelativeDimension` | part (3) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/FibreDimension/RelativeDimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 2 are kept. The 5 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.RelativeDimensionLE`, `AlgebraicGeometry.RelativeDimensionLE.at`, `AlgebraicGeometry.RelativeDimensionLEAt`, `AlgebraicGeometry.relativeDimensionLEAt_iff`, `AlgebraicGeometry.relativeDimensionLE_iff`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
