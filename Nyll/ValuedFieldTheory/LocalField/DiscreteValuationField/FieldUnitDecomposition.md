# The decomposition Kˣ ≅ μ × U¹ × ℤ

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitDecomposition`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a complete discretely valued field with finite residue field of order `q`, and `π` a uniformizer. This file proves that every unit of `K` is uniquely a product `ζ · u · πⁿ` of a lifted residue root of unity `ζ`, a first principal unit `u` and an integer power of `π`, and that the resulting group isomorphism `μ × U¹ × ℤ ≅ Kˣ`, with `μ` the group of lifted residue roots of unity, of order `q − 1`, is a homeomorphism for the valuation topology.

## Main definitions and results

- `exists_roots_principalUnit_uniformizer_zpow_of_completeDVF` (existence) and `roots_principalUnit_uniformizer_zpow_eq_iff_of_completeDVF` (uniqueness), for a `CompleteDVF` with finite residue field and a uniformizer `π`. Here `ζ` ranges over `residueRootsOfUnityGroup F` and `u` over `higherPrincipalUnitGroup F 1`.
- `fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF : fieldUnitDecompositionFactors F ≃* Kˣ`, with simp lemmas saying that the `ℤ`-component of the inverse is the valuation exponent `uniformizerValueExponent F hπ x`.
- `fieldUnitUniformizerUnitPart`: the unit `x · π^(−v(x))` of the valuation ring; the `μ × U¹` part of the inverse is the decomposition of this unit (`fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_fst_eq_unitPart`).
- Topological lemmas, all for the valuation topology `mrangeRestrictValued F` (the valuation with value group cut down to its image): the exponent is locally constant, hence continuous; `U¹` is open in the units of the valuation ring; the residue map on units is locally constant; the map `Oˣ → μ × U¹` inverse to `valuationSubringUnitsEquivRootsTimesPrincipalUnits F`, the unit part, the forward product map and the inverse map are continuous.
- `fieldUnitsContinuousMulEquivRootsPrincipalUnitsUniformizer_of_completeDVF_mrangeRestrict`: the decomposition as an isomorphism of topological groups `≃ₜ*`.
- `exists_roots_principalUnit_uniformizer_zpow_of_withZeroValuation` and `roots_principalUnit_uniformizer_zpow_eq_iff_of_withZeroValuation`: existence and uniqueness for a valuation `v : K → ℤᵐ⁰` that is complete discrete with finite residue field, and an element `ϖ` with `v(ϖ) = exp(−1)`.

## Proofs

The algebraic statements are transported from an abstract decomposition, proved elsewhere for any integer valuation on `Kˣ` whose valuation-zero subgroup is the unit group of the valuation ring, together with a uniformizer for that valuation. That valuation is supplied by `multiplicativeIntegerValuationOfUniformizer` (or by `ofWithZeroValuation` in the `ℤᵐ⁰` case). Continuity is checked factor by factor, using that the `μ`-factor depends only on the residue class and the exponent only on the valuation.

## Points to watch

- The decomposition depends on the chosen uniformizer.
- The topology on `K` is the range-restricted valued topology, introduced locally by `let` inside each statement rather than as a global instance.
- In the `ℤᵐ⁰` form the uniformizer must be normalized by `v(ϖ) = exp(−1)`, and `IsCompleteDiscrete` is the library's class.
- No topological statement is given in this file for the `ℤᵐ⁰` form.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/FieldUnitDecomposition.lean`: the Lean file is the source byte for byte (SHA-256 `f49fe8869b5ec85dcc2006c3843acefe6651dc86eb6ca4a72dd880fe650454c1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
