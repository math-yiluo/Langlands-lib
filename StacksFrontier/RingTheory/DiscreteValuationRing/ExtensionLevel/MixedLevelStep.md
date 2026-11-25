# Weak solutions and the finite-support level step

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.MixedLevelStep`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a tower of discrete valuation rings A → B → C with fraction fields K → L → M, the file describes the output of a mixed-characteristic level step and converts a descended cyclotomic parameter into that output.

- `MixedLevelStepOutcome` asserts the existence of a finite separable, totally ramified extension of K giving a weak solution or a degree-p layer over tensor fields of level at most max(0, ℓ − 1, 2ℓ − p). `MixedLevelPreparation` records the least numerator n, the precision m = min(n, e, pe − n), and the generating equation and Laurent approximation modulo πᵐ after scaling by πⁿ. Its residue polynomial has coefficients in the perfect core. `MixedLevelStepReentry` asserts the outcome over a compatible weakly unramified base with perfect residue field once the finite coefficient set is in its residue image and the chosen uniformizer maps to π.
- `mixedLevelStepOutcome_of_scaled_parameter_eq` proves the outcome for a positive least numerator in a finite-level cyclotomic presentation, under weakly unramified A → B and perfect base residue field in characteristic p. It takes `haA`, the congruence of πⁿξ to an element of A modulo πᵐB, and `hbound`, the equality of (n − m)/e with the asserted bound.
- `mixedLevelStepOutcome_or_numerator_lt_of_mapped_preparation` uses a prepared polynomial mapped along weakly unramified B₀ → B, with matching uniformizer images from B₀ and A and absorbed perfect-core coefficients. It gives the outcome or a least numerator in B strictly below the supplied n. Both outcome theorems take `hP`, giving `intProp`, `quotChar`, `shapeProp` and `funcEq` for P over B, and `hfinite` for M/L over B; the mapped theorem's polynomial over B₀ is separate.
- `exists_isWeakSolution_of_tensor_embedding` handles a finite Galois layer embedded in the lower tensor field. `exists_isWeakSolution_of_unramified_normalization` handles two tensor fields when the upper normalization is a discrete valuation ring whose maximal ideal extends from the intermediate one. Both take a finite separable extension E of the characteristic-zero field K, a generator of M over L, and `hfrac` making L ⊗ₖ E the fraction field of the integral closure of B in it, and assume the lower two integral closures are discrete valuation rings with a compatible map extending the maximal ideal. `nonempty_algHom_of_cyclotomic_tensor_not_isField` supplies the embedding: for a generating degree-p presentation with `intProp f P` and `wElt f ≠ 0`, if L ⊗ₖ E is a field and M ⊗ₖ E is not, M embeds into L ⊗ₖ E over L.

The three abbreviations for the level step express propositions. In the mapped theorem `habs` supplies absorption of the finite residue support, and the second alternative compares numerators over B. The main step and weak-solution criteria use one universe for the rings and fields.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ExtensionLevel/MixedLevelStep.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
