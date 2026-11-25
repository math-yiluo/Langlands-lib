# Local fibre dimension on affine charts

Module `StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The local topological Krull dimension in a fibre can be computed on any compatible pair of affine charts.

`fiberDimensionAt_specMap` identifies this dimension at a prime q of a commutative R-algebra B with `Algebra.relativeDimensionAt R q.asIdeal`. `fiberDimensionAt_eq_relativeDimensionAt_chart` gives the general chart formula using the map on sections for a source affine open contained in the inverse image of a target affine open.

`fiberDimensionAt_comp_openImmersion` preserves local fibre dimension under precomposition by an open immersion. `fiberDimensionAt_comp_embedding` gives invariance under postcomposition with any morphism injective on points.

These comparisons identify the scheme-theoretic fibre homeomorphically with the set-theoretic fibre. The source restriction gives an open subspace of the fibre, and an injective target map leaves the set-theoretic fibre equal.

The module docstring also lists a comparison along a commuting square of open immersions, which the file does not contain.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/FibreDimension/Comparison.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 6 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.fiberDimensionAt_eq_of_open_square`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
