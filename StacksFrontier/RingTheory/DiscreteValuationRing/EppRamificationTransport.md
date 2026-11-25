# Ramification indices under ring isomorphisms

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppRamificationTransport`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves invariance of a Mathlib ramification index under a commuting square of commutative rings R → S and R′ → S′ with vertical ring isomorphisms e : R ≃+* R′ and e′ : S ≃+* S′, the hypothesis `hsq` saying that `algebraMap R' S' (e x) = e' (algebraMap R S x)`.

`ramificationIdx_map` concerns `Ideal.ramificationIdx`, defined by the length of a quotient of the localization at a prime q of S. It equates that index over R with the index of the image prime over R′.

Transports along ring isomorphisms serve the proof: `map_eq_comap_symm` (`Ideal.map` along e is `Ideal.comap` along its inverse), `isPrime_map` (primality), `map_primeCompl` (the prime complement) and `under_map` (`Ideal.under` along the square). The proof transports the prime, its contraction and its prime complement to obtain an isomorphism of localizations matching the quotient ideals. `quotient_length_eq` uses the induced order isomorphism on submodules to compare lengths.

The module docstring also announces results on `Ideal.ramificationIdx'`, the supremum of the admissible exponents; the file does not contain them.

The comments refer to Tag 09F5.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppRamificationTransport.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 6 are kept. The 3 left out are not needed by the results for which the extract is made: `Stacks.DiscreteValuationRing.EppLevelInduction.map_le_pow_iff_of_ringEquiv_square`, `Stacks.DiscreteValuationRing.EppLevelInduction.ramificationIdx'_eq_of_ringEquiv_square`, `Stacks.DiscreteValuationRing.EppLevelInduction.ramificationIdx'_maximalIdeal_eq_of_ringEquiv_square`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
