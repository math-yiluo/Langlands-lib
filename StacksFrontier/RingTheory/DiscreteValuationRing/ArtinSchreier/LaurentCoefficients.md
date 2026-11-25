# Laurent coefficient numerators and uniformizers under weakly unramified extensions

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.LaurentCoefficients`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file turns Laurent coefficient data into a single numerator and shows that weakly unramified DVR extensions preserve uniformizers.

`IsDiscreteValuationRing.eq_constant_numerator_of_coefficients_lift` takes compatible maps A → B → L with L a field, π ∈ A with nonzero image in L, and πⁿξ equal to the image of ∑ cᵢπⁱ (i < n) + πⁿb (cᵢ, b ∈ B). Given lifts from A of the cᵢ modulo πⁿB, it writes ξ as π⁻ⁿ times the sum of the lifts weighted by powers of π, plus an element of B. The proof absorbs the errors, divisible by πⁿ, into the integral term; the lifts are arguments, so the numerator is an explicit term.

`irreducible_algebraMap_of_isWeaklyUnramified` shows that every uniformizer of A maps to a uniformizer of B when the extension of DVRs A → B (`IsExtension`, an injective local map) is weakly unramified (`IsWeaklyUnramified`, ramification index one).

The module docstring and the docstring of `eq_constant_numerator_of_coefficients_lift` announce results not in the file: an Artin–Schreier extension, the trichotomy for a minimal numerator, the residue of the numerator and an existential form.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ArtinSchreier/LaurentCoefficients.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 11 declarations of the source file 2 are kept. The 9 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.artinSchreier_trivial_or_unramified_or_totallyRamified_of_laurent_coefficient_roots`, `IsDiscreteValuationRing.artinSchreier_trivial_or_unramified_or_totallyRamified_of_minimal_numerator_root`, `IsDiscreteValuationRing.artinSchreier_trivial_or_unramified_or_totallyRamified_of_unit_numerator`, `IsDiscreteValuationRing.exists_constant_numerator_of_coefficients_lift`, `IsDiscreteValuationRing.exists_isGalois_totallyRamified_artinSchreier`, `IsDiscreteValuationRing.exists_pow_eq_and_not_pow_of_not_range`, `IsDiscreteValuationRing.exists_pow_eq_and_not_pow_of_perfectCore_le`, `IsDiscreteValuationRing.isUnit_of_minimal_poleOrder`, `IsDiscreteValuationRing.residue_sum_mul_uniformizer_pow`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
