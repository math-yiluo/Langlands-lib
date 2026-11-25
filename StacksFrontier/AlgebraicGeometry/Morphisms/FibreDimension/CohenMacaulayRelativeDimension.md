# Pure relative dimension with Cohen–Macaulay fibres

Module `StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A flat scheme morphism locally of finite presentation with Cohen–Macaulay fibres has locally constant relative dimension on the source. Its dimension level sets give a canonical decomposition into open and closed subschemes.

## Dimension function and pieces

- `relativeDimensionFunction` takes values in the natural numbers. By `relativeDimensionFunction_apply`, its value at x, coerced to `WithBot ℕ∞`, is the local topological Krull dimension at `f.asFiber x` in the fibre over f(x).
- `relativeDimensionOpen` is the level set for a given dimension d. The canonical opens are closed (`relativeDimensionOpen_isClopen`), pairwise disjoint (`pairwise_disjoint_relativeDimensionOpen`) and cover the source (`iSup_relativeDimensionOpen`). `relativeDimensionOpen_relativeDimension` gives `RelativeDimension` d for the restricted morphism, so every nonempty fibre of that restriction is equidimensional of dimension d. `exists_clopen_relativeDimension` packages these conclusions.
- For a scheme locally of finite type over a field, `equidimensional_of_constant_fiber_local_dimension` derives equidimensionality from constant local dimension by testing generic points of components.

Local finite presentation makes each pointwise fibre dimension a natural number. For local constancy, affine charts identify it with `Algebra.relativeDimensionAt` and identify the Cohen–Macaulay condition with the one on the localized quotient fibre ring. The proof applies `Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_relativeDimensionAt_eq` and transports the open set back. On each level set, the local dimension survives open restriction and gives the dimension of every nonempty fibre by taking its supremum over the fibre.

The dimension function and decomposition take `hCM`, Cohen–Macaulayness of every scheme-theoretic fibre, as an explicit hypothesis.

Tag 02NM.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02NM](https://stacks.math.columbia.edu/tag/02NM) | `relativeDimensionFunction` | relative dimension function |
| [02NM](https://stacks.math.columbia.edu/tag/02NM) | `relativeDimensionFunction_apply` | pointwise relative dimension |
| [02NM](https://stacks.math.columbia.edu/tag/02NM) | `relativeDimensionOpen` | canonical dimension pieces |
| [02NM](https://stacks.math.columbia.edu/tag/02NM) | `relativeDimensionOpen_isClopen` | canonical pieces are clopen |
| [02NM](https://stacks.math.columbia.edu/tag/02NM) | `iSup_relativeDimensionOpen` | canonical pieces cover |
| [02NM](https://stacks.math.columbia.edu/tag/02NM) | `pairwise_disjoint_relativeDimensionOpen` | canonical pieces are disjoint |
| [02NM](https://stacks.math.columbia.edu/tag/02NM) | `relativeDimensionOpen_relativeDimension` | canonical pieces have pure relative dimension |
| [02NM](https://stacks.math.columbia.edu/tag/02NM) | `exists_clopen_relativeDimension` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/FibreDimension/CohenMacaulayRelativeDimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 20 declarations of the source file 19 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.fiber_local_dimension_eq_of_equidimensional`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
