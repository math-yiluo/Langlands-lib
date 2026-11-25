# Lifting generic points of a relative normalization

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeGenericPoints`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Every generic point of an irreducible component of a relative normalization is the image of a generic point of an irreducible component of the source.

`exists_genericPoint_irreducibleComponent_mapping_to` takes a quasi-compact, quasi-separated morphism f : Y ⟶ X, a component Z of its relative normalization and a generic point x of Z. It gives a component of Y and a generic point y of that component such that `f.toNormalization y = x`.

Dominance first gives a point above x. Choose the generic point of a source component containing that point. Its image generalizes x, and maximality of Z as an irreducible closed subset forces that image to equal x.

Reference is Stacks Project Tag 0AXP.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0AXP](https://stacks.math.columbia.edu/tag/0AXP) | `exists_genericPoint_irreducibleComponent_mapping_to` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/RelativeGenericPoints.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
