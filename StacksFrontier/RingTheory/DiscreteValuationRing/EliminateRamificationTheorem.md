# Elimination of ramification for discrete valuation rings

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationTheorem`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

An essentially finite type extension of discrete valuation rings A → B with fraction fields K → L admits a finite extension K₁/K that eliminates ramification in the normalized base change.

`exists_finite_extension_isSolution` proves this as an `IntegralClosureBaseChange.IsSolution`. The map from the integral closure of A in K₁ to that of B in the reduction of L ⊗[K] K₁ is formally smooth for the maximal-ideal-adic topology after localizing at each target maximal ideal and its contraction.

`exists_finite_extension_isSolution_of_eppTheorem_monomorphic` derives the same result assuming Epp’s theorem at two single-universe profiles. The hypothesis `hMono` uses the maximum of the universes of A, B, K and L. The hypothesis `hMonoLocal` uses the maximum of the universes of K and L. The unconditional proof supplies both from the universe-polymorphic theorem `Stacks.EppTheorem.eppTheorem_monomorphic`.

References are Stacks Project Tag 09II for the conclusion and Tag 09F9 for Epp’s theorem.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09II](https://stacks.math.columbia.edu/tag/09II) | `exists_finite_extension_isSolution` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EliminateRamificationTheorem.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
