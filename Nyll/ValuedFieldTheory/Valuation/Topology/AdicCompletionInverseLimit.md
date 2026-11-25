# Units of complete rings as inverse limits

Module `Nyll.ValuedFieldTheory.Valuation.Topology.AdicCompletionInverseLimit`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a ring `R` complete for an ideal `I`, and a complete discrete valuation ring `𝒪` with uniformizer `π`, this file describes the unit group as a projective limit: `Rˣ ≅ lim (R/Iⁿ)ˣ` and `𝒪ˣ ≅ lim 𝒪ˣ/U⁽ⁿ⁺¹⁾`, where `U⁽ⁿ⁾ = {u : u − 1 ∈ πⁿ𝒪}`, the latter also as a homeomorphism onto the limit of the discrete quotients. These are then specialized to complete discretely valued fields.

## Adically complete rings

- `adicCompletionUnitsEquiv`: `Rˣ ≃* (AdicCompletion I R)ˣ`; `adicCompletion_units_coordinates_injective` and `adicCompletion_units_coordinates_surjective`: a unit is determined by its reductions mod `Iⁿ`, and every unit of the completion comes from one.
- `unitsModIdealEquivQuotientUnits`: `Rˣ/ker(Rˣ → (R/I)ˣ) ≃* (R/I)ˣ` when `R → R/I` is a local homomorphism; `unitsModMaximalIdealPowEquiv` is the case `I = 𝔪ⁿ` of a local ring, `n ≥ 1`.
- `adicUnitInverseLimit I` and `adicPositiveUnitInverseLimit I`: compatible families in `(R/Iⁿ)ˣ`, `n ≥ 0`, resp. `(R/Iⁿ⁺¹)ˣ`, isomorphic by `adicUnitInverseLimitEquivPositive`. `unitsEquivUnitInverseLimit` and `unitsEquivPositiveUnitInverseLimit` give `Rˣ` as these limits, coordinatewise by reduction.

## Higher units of a discrete valuation ring

- `dvrPowerIdealUnitInverseLimit π` (limit of `(𝒪/πⁿ⁺¹𝒪)ˣ`) and `dvrHigherUnitQuotientInverseLimit π` (limit of `𝒪ˣ/U⁽ⁿ⁺¹⁾`), compared by `higherUnitQuotientInverseLimitEquivPowerIdealUnitInverseLimit`.
- `dvrUnitsEquivHigherUnitQuotientInverseLimit`: for a DVR `𝒪`, `π` irreducible and `𝒪` complete for `(π)`, `𝒪ˣ ≃* lim 𝒪ˣ/U⁽ⁿ⁺¹⁾`, coordinatewise `u ↦ u mod U⁽ⁿ⁺¹⁾`.
- The limit carries the topology from its discrete stages. `unitsEquivHigherUnitQuotientInverseLimitHomeomorph` is the isomorphism as a homeomorphism, for the topology on `𝒪ˣ` induced by the `(π)`-adic topology (`adicUnitsTopology`).

## Complete valued fields

- Declarations prefixed `completeDVF_`: `adicCompletionUnitsEquiv`, the two coordinate statements, `unitsModMaximalIdealPowEquiv` and `unitsEquivUnitInverseLimit` for a `CompleteDVF` and its maximal ideal, plus `𝒪 ≅ AdicCompletion` and `𝒪 ≅ lim 𝒪/𝔭ⁿ`.
- For `K` complete with a rank-one discrete valuation, with the valuation topology: `completeValuedField_valuationSubringEquivPositiveQuotientInverseLimit` and `completeValuedField_valuationSubringPositiveQuotientInverseLimitHomeomorph` give `𝒪 ≅ lim 𝒪/𝔪ⁿ⁺¹` as rings and spaces; for a uniformizer `π`, `completeValuedField_unitsEquivHigherUnitQuotientInverseLimit` and `completeValuedField_unitsHigherUnitQuotientInverseLimitHomeomorph` do the same for `𝒪ˣ`. Helpers: `π` is irreducible, `(π) = 𝔪`, and `𝒪` is `(π)`-adically complete.

## Proofs

Units of the adic completion are matched with compatible unit families, the `n = 0` coordinate is dropped, and an earlier isomorphism `𝒪ˣ/U⁽ⁿ⁾ ≅ (𝒪/πⁿ𝒪)ˣ` passes to higher units.

## Points to watch

- The limits are the library's own types, built from compatible families, not Mathlib limits; in the positive versions coordinate `n` is level `n + 1`.
- `higherUnitSubgroup`, `uniformizerPowerIdeal` and the higher-unit limit make sense for any element `π` of any commutative ring; comparing the two limits needs a DVR and `π` irreducible; the isomorphisms with `𝒪ˣ` also need `(π)`-adic completeness as an instance.
- The DVR homeomorphism uses the `(π)`-adic topology on a `WithTopology` copy of `𝒪ˣ`; only the valued-field versions use the valuation topology, and they also assume `MulArchimedean Γ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Topology/AdicCompletionInverseLimit.lean`: the Lean file is the source byte for byte (SHA-256 `7904519172f43adbaa8622255ab01f66d7d84d34b3ae70cd94b39078a81c6758`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
