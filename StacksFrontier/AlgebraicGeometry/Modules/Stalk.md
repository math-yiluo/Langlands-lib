# Module structure on a scheme stalk

Module `StacksFrontier.AlgebraicGeometry.Modules.Stalk`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For any sheaf of modules F on a scheme X and any point x, the stalk of F at x is a module over the local ring of X at x.

`AlgebraicGeometry.Scheme.Modules.moduleStalk` applies the Mathlib presheaf-of-modules construction to the underlying presheaf `F.val.presheaf`. `moduleStalkPresheaf` supplies the same action for the stalk written as `F.presheaf.stalk x`, the form used by the scheme-module germ maps.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Modules/Stalk.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
