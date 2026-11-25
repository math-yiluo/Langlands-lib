# Transitivity of relative flatness for modules

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Module`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Flatness of a sheaf of modules over a base at a point can be composed with flatness of a morphism out of that base at the image point.

For ringed-space morphisms f : X ⟶ Y and g : Y ⟶ Z, `IsFlatOverAt.comp` proves that a sheaf of modules F on X is flat over Z at x if `IsFlatOverAt` holds for F over Y at x and `IsFlatAt` holds for g at f(x). The statement applies to arbitrary sheaves of modules on ringed spaces in the common universe.

The stalk map of the composite is the composite of the stalk maps. This supplies the scalar tower on the module stalk for `Module.Flat.trans`.

Reference is Stacks Project Tag 01U6.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01U6](https://stacks.math.columbia.edu/tag/01U6) | `comp` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Flat/Module.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
