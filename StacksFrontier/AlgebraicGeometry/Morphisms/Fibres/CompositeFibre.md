# The fibre of a composite

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.CompositeFibre`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The fibre of a composite over a point of its final target is obtained by pulling back the fibre of the second morphism along the first.

For morphisms i from A to B and g from B to S and a point s of S, `AlgebraicGeometry.fiberMapOfSourceHom` maps the fibre of `i ≫ g` at s to the fibre of g at s. Its projection identities give compatibility with i on the total spaces and with the structure maps to Spec κ(s). `fiberMapOfSourceHom_isPullback` makes the square with the two fibre inclusions and i Cartesian.

The comparison is a pullback lift, and the Cartesian property follows by cancellation of the fibre square for g.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Fibres/CompositeFibre.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
