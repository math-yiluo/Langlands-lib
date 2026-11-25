# Generic points of fibres and generalizations

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.GenericPointGeneralizing`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A point of a scheme is generic in a component of its own fibre exactly when every generalization in that fibre equals the point itself.

`AlgebraicGeometry.mem_genericPoints_asFiber_iff` formulates this in terms of generalizations in the source with the same image. By `mem_genericPoints_asFiber_of_generalizingMap`, if π lifts generalizations and y is generic in a fibre component for `π ≫ f`, then π(y) is generic in a fibre component for f. The proof uses the homeomorphism with the set-theoretic fibre and lifts each generalization of π(y).

The module docstring also announces, for flat morphisms of locally Noetherian schemes, a converse of the coheight computation at a generic point of a fibre and the resulting equivalence; neither is in this file.

Stacks Project, Tag 09IL and Tag 00ON.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Fibres/GenericPointGeneralizing.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 2 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.coheight_eq_coheight_base_iff_asFiber_mem_genericPoints`, `AlgebraicGeometry.mem_genericPoints_asFiber_of_coheight_eq`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
