# Cyclotomic generator preparation and descent of scaled parameters

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.ScaledParameter`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file prepares polynomial equations used to control the level of a prime-degree extension of the fraction field of a discrete valuation ring. It changes generators modulo a uniformizer power and descends scaled parameters along the coefficients of the prepared polynomial.

- `exists_generator_no_pow_related_coefficients` starts with a generator z with P(z) = ξ, for the cyclotomic quotient polynomial P, and an approximation F(π⁻¹) with πⁿ(ξ − F(π⁻¹)) divisible by πᵐ in the base DVR. It assumes the cyclotomic element w is associated to πᵉ, with n < pe, m ≤ e and n + m ≤ pe. P is supplied with the integrality, shape and addition-law conditions `intProp`, `shapeProp` and `funcEq`, and reduces to Xᵖ − X where w maps to zero. A polynomial over a characteristic-p ring matches F in the quotient by πᵐ and has constant coefficient in a subring S. Both approximating polynomials have degree at most n. The replacement preserves generation and the form of the congruence. Among coefficients outside S, no monomial exponent is a positive p-power multiple of another.
- `exists_root_heights_and_unique_max` assumes S consists of elements with pʳ-th roots for every r ≥ 1 and there is a coefficient outside S. Under the exponent condition, it extracts roots μᵢ of heights hᵢ which are themselves not pth powers, and chooses N so that the exponents i · p^(N − hᵢ) have a unique maximum. In characteristic p, `exists_comp_X_pow_add_pow_sub` takes N > 0 and, for every index i of the support of a polynomial Q (not only those with coefficient outside S), a height hᵢ ≤ N and a root μᵢ with μᵢ^(p^(hᵢ)) equal to the i-th coefficient; a Frobenius correction Gᵖ − G added to Q(X^(pᴺ)) then gives the sum of μᵢ X^(i · p^(N − hᵢ)) over the support.
- `isDegreePExtensionOfFiniteLevel_and_extensionLevel_le_of_associated_pow` gives finite level at most n/e for a degree-p extension when ϖ is associated to πᵈ and w to ϖᵉ, with d, e > 0, ϖⁿξ in the base DVR, and n < pe.
- `exists_scaled_parameter_eq_of_coefficients_descend` assumes the residue coefficients come from the base via compatible residue-section and quotient maps. Given the scaled parameter congruence, it writes πⁿξ as an element from the base plus a multiple of πᵐ in the upper ring. `exists_scaled_parameter_eq_of_quotient_coefficients_descend` is the form with the descent stated in the truncated quotients, and `exists_mapped_scaled_parameter_relation` carries the congruence along a commuting base-change square.

Telescoping Frobenius sums give the corrections Gᵖ − G. The cyclotomic addition law realizes the first correction on the generator.

The level estimate uses the library's level predicates and places the DVR and both fields in a single universe.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ExtensionLevel/ScaledParameter.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 24 declarations of the source file 21 are kept. The 3 left out are not needed by the results for which the extract is made: `Stacks.DiscreteValuationRing.EppLevelInduction.exists_scaled_parameter_eq_of_mapped_preparation`, `Stacks.DiscreteValuationRing.EppLevelInduction.polynomial_map_coeff_mem_fieldRange_of_support`, `Stacks.DiscreteValuationRing.EppLevelInduction.polynomial_quotient_relation_map`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
