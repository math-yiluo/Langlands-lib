# A source point in a specified fibre

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourcePoint`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A point x of the source of f determines a point of the fibre over any y identified with f(x).

`AlgebraicGeometry.Scheme.Hom.asFiberAt f x y h` takes an equality `h : f x = y` and returns a point of `f.fiber y`. The definition transports Mathlib’s `f.asFiber x` along h. With the reflexivity proof it reduces to that original point.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Fibres/SourcePoint.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
