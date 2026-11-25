# Stalk maps for a field extension

Module `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.PullbackStalk`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The morphism of spectra induced by a field extension respects the canonical maps from the ground field to the local rings.

`AlgebraicGeometry.stalkMap_spec_comp_algebraMap` takes a field extension K/k, a point y of Spec K and a point z of Spec k identified with its image. The map from k to the stalk at z followed by the induced stalk map equals the composite from k through K to the stalk at y.

The proof substitutes the image of y for z and applies `stalkMap_toStalk_apply` elementwise. The point equality is explicit in the statement and transports the source stalk via `eqToHom`. Both fields lie in the same Lean universe.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Variety/Geometrically/PullbackStalk.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
