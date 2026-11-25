# Descent of tame weak solutions from completion

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionTame`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file carries out the completion step for the tame and residue-characteristic-zero cases of Epp’s theorem. It works with a discrete valuation ring extension A → B and compatible fraction fields K → L, with no completeness assumption on A or B.

- `isWeakSolution_canonicalBaseChange_adicCompletion` proves that any finite extension K₁/K yields a weak solution for A → Â with the canonical integral-closure base change.
- `isWeakSolution_canonicalBaseChange_of_tensorProduct_algEquiv` takes a finite extension K₁/K, a finite extension M/K̂ giving a weak solution for Â → B̂, and a K̂-algebra equivalence K̂ ⊗[K] K₁ ≃ M. It gives a weak solution for A → B with the canonical data over K₁.
- `exists_finite_extension_isWeakSolution_of_isSeparable_adicCompletion` takes the existence of a finite separable weak solution upstairs and produces a finite separable weak solution downstairs.
- `exists_finite_extension_isWeakSolution_of_tame_or_charZero_of_isDVR` supplies that solution when the base residue characteristic is zero, or when it is coprime to the ramification index and the residue extension is separable.

Adic formal smoothness of A → Â gives the weak solution along that map by propagation through finite base change. Krasner’s theorem gives the tensor-product equivalence in the separable case. Composition and descent of weak solutions then give the result over A → B, using the complete tame theorem on Â → B̂.

The general transport theorem takes the upstairs weak solution as `hup` and the equivalence as `e`. The existence version uses separability in `hup` to obtain `e`. In both, M must lie in the universe of A, and in the transport theorem K₁ lies in the universe of K. The final theorem covers the tame and residue-characteristic-zero cases of Tag 09F9.

The cited ingredients are Tag 09E7 and Tag 09EQ for formal smoothness, Tag 09EJ for descending the finite separable extension, and Tag 09ES for composition and descent.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppCompletionTame.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
