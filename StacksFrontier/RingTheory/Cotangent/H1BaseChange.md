# Flat base change for cotangent homology

Module `StacksFrontier.RingTheory.Cotangent.H1BaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let S be an R-algebra and S′ its base change along a flat map R → R′ of commutative rings. This file identifies the first homology of the naive cotangent complex after base change.

In `Stacks.Cotangent.H1BaseChange`, `isBaseChange_restrictScalars_h1Cotangent_map` says the canonical map on H₁ identifies the target with R′ ⊗[R] H₁(S/R). The theorem `isBaseChange_h1Cotangent_map` identifies the same target with S′ ⊗[S] H₁(S/R) through the same map.

The proof transports Mathlib’s `Algebra.tensorH1CotangentOfFlat` across the pushout isomorphism. The composition law `h1Cotangent_map_map` identifies the transported map with the canonical one. The general lemma `isBaseChange_of_isBaseChange_of_isPushout` then changes the base ring from R′ to S′ by cancelling successive tensor products.

Both base-change identifications for H₁ assume that R′ is flat over R.

The reference is Stacks Project Tag 00S4.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Cotangent/H1BaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
