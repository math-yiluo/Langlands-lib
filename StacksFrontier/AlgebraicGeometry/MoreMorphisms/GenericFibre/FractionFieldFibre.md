# The generic fibre as a fraction-field base change

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FractionFieldFibre`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a domain A with fraction field K and any morphism g from Y to Spec A, the fibre over the generic point η is the base change to Spec K.

`AlgebraicGeometry.exists_isIso_isPullback_fiberι_genericPoint` gives the pullback square after identifying Spec κ(η) with Spec K. The proof uses the A-algebra isomorphism of the two fraction fields. `CategoryTheory.IsPullback.comp_isIso_right` moves that isomorphism across the square.

`exists_dense_open_smooth_fiber_genericPoint_of_isPullback` takes any presentation of the base change as a pullback and assumes a dense open there smooth over Spec K. It transports that open to the generic fibre, preserving density by the comparison homeomorphism and smoothness by composition with isomorphisms.

References include Tag 09IL and Tag 0559.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/GenericFibre/FractionFieldFibre.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
