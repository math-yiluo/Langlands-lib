# Openness of fibrewise exactness

Module `StacksFrontier.RingTheory.Flat.FiberExactLocus`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a finite complex of finite free modules over a flat finite-type algebra S over a Noetherian ring R, the file proves openness of the fibrewise exact locus under Cohen–Macaulay and equidimensionality hypotheses. At a prime q of S the complex is tensored with S_q/pS_q, where p is the contraction of q to R.

## Definitions and results

- `Stacks.Flatness.FibreExactnessLocus.BaseChangeExact` is the file's predicate for exactness of the complex after extension to an S-algebra. It requires injectivity of the leftmost differential and exactness at every interior term.
- In the same namespace, `isOpen_setOf_baseChangeExact_localization` proves openness of exactness after localization at q for finite modules over a Noetherian ring. `baseChangeExact_localization_of_baseChangeExact_fiber` shows that fibre exactness at q implies localized exactness there for finite free modules over S flat over R, with both rings Noetherian.
- `Algebra.isOpen_setOf_exact_baseChange_fiber_of_flat_of_isMaximalCohenMacaulay_of_equidimensional` proves that the fibrewise exact locus is open in Spec(S) under the hypotheses above. The proof produces a principal open neighbourhood of each point in the locus.

The local flatness criterion lifts fibre exactness to the localization, where exactness is open by closedness of the supports of the finite homology modules. On that open set the Buchsbaum–Eisenbud criterion reduces fibre exactness to depth bounds of k + 1 on the ideals of expected-rank minors of the k-th differential, and openness for fibrewise regular sequences makes each bound persist near the point.

## Scope and references

This is the equidimensional case of Tag 00RB. The hypothesis `hfib` requires Cohen–Macaulayness at every local ring of every nonempty fibre and an equidimensional spectrum of a common finite Krull dimension d. For Tag 00RB with just Cohen–Macaulay fibres of dimension d, the module docstring and the theorem's docstring refer to `Algebra.isOpen_setOf_exact_baseChange_fiber_of_flat_of_isMaximalCohenMacaulay` in `StacksFrontier.RingTheory.Flat.FiberExactLocusFlat`; that module is not in this repository.

The proof uses Tag 00MI for the local criterion, Tag 00N1 for the determinantal criterion, Tag 00RA for regular-sequence openness and Tag 02JN for regularity in a Cohen–Macaulay local ring.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/FiberExactLocus.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 48 declarations of the source file 47 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.Flatness.FibreExactnessLocus.mem_smul_top_of_injective_baseChange`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
