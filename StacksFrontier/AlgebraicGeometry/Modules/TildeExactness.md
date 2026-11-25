# Left exactness of the affine associated-sheaf functor

Module `StacksFrontier.AlgebraicGeometry.Modules.TildeExactness`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative ring R, the functor taking an R-module M to its associated sheaf on Spec R is exact.

`AlgebraicGeometry.tilde.preservesFiniteLimits` supplies preservation of finite limits for `tilde.functor R`. The existing adjunction with global sections supplies right exactness.

The proof tests exactness of the image of an exact short complex on all stalks. At a prime ideal, the associated-sheaf maps on stalks are the localizations of the module maps. Exactness of module localization gives exactness there, and the criterion for additive exact functors gives preservation of finite limits.

Stacks Project, Tag 01HV.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Modules/TildeExactness.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
