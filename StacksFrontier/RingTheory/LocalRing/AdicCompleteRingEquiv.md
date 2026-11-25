# Adic completeness under local ring isomorphisms

Module `StacksFrontier.RingTheory.LocalRing.AdicCompleteRingEquiv`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

An isomorphism of local rings transports completeness for the maximal-ideal-adic filtration.

`isAdicComplete_maximalIdeal_of_ringEquiv` takes an isomorphism e between commutative local rings S and T and a maximal-ideal-adic completeness instance on S, and gives the corresponding instance on T. The image of the maximal ideal of S is maximal and hence equals the maximal ideal of T. The proof then applies Mathlib's `IsAdicComplete.congr_ringEquiv`.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/LocalRing/AdicCompleteRingEquiv.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
