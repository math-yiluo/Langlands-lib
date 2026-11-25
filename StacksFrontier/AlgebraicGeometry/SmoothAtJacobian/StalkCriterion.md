# A stalk criterion for smoothness at a point

Module `StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.StalkCriterion`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file relates smoothness near a source point x to formal smoothness of the induced local-ring map.

`Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus` assumes f locally of finite presentation. It identifies smoothness at x (`Condition1`, that is smoothness on a neighbourhood of x) with membership in `Scheme.Hom.smoothLocus`, which means formal smoothness of the stalk map. The forward direction uses formal smoothness of stalk maps on smooth neighbourhoods. The reverse invokes `exists_smooth_of_formallySmooth_stalk` to obtain a smooth affine neighbourhood.

The module docstring also announces that smoothness at x makes the stalk map flat, the flatness conjunct of condition (2); that result is not in the file.

See Tag 01V9.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/SmoothAtJacobian/StalkCriterion.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.SmoothAtJacobian.condition1_imp_flat_stalkMap`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
