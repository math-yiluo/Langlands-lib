# The valuation sequence 1 → 𝒪ˣ → Kˣ → ℤ → 0 of a nonarchimedean local field

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field `K`, the file builds the normalized valuation `Kˣ → ℤ` as a group homomorphism, proves that its kernel is the image of the units of the valuation ring and that it is onto, and deduces `Kˣ / 𝒪[K]ˣ ≃ ℤ` and the decomposition of a unit as a unit of `𝒪[K]` times a power of a fixed element of valuation one.

## Main definitions

- `valuationUnitsMulHom K : Kˣ →* Multiplicative ℤ`: the valuation of `K`, transported along the isomorphism of its value group with zero onto `ℤᵐ⁰` (`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`), restricted to units.
- `valuationMap K : Additive Kˣ →+ ℤ`: the same map written additively; `valuationMap_apply` identifies it with the library's normalized valuation `v K`. `valuationShortComplex` is a second name for the same homomorphism.
- `uniformizerFieldUnit K π hπ`: a uniformizer `π ∈ 𝒪[K]` for the valuation, as a unit of `K`.
- `integerUnitOfValuationMapZero`: a unit of `K` of valuation zero, as a unit of `𝒪[K]`.
- `fieldUnitsModIntegerUnitsAddEquivInt K`: the isomorphism `Kˣ / 𝒪[K]ˣ ≃+ ℤ` (written additively) induced by `valuationMap`.
- `uniformizerUnitFactor K ϖ hϖ x`: for `ϖ` with `valuationMap ϖ = 1`, the unit `x / ϖ^(v(x))` of `𝒪[K]`.
- `chosenValuationMapSection`: a set-theoretic right inverse `ℤ → Kˣ` of `valuationMap`, chosen by choice.

## Main results

- `valuationMap_surjective`, `valuationMap_uniformiser`: the valuation is onto, and some unit has valuation 1.
- `valuationMap_uniformizerFieldUnit`: a uniformizer of `𝒪[K]` has valuation `−1`.
- `additiveIntegerUnitsToFieldUnits_range_eq_ker_valuationMap`, `integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero`: exactness at `Kˣ`; a unit of `K` lies in `𝒪[K]ˣ` if and only if its valuation is zero.
- `mem_powMonoidHom_range_integerUnits_iff`: for `n ≥ 1`, a unit of `𝒪[K]` is an `n`-th power in `𝒪[K]ˣ` if and only if it is one in `Kˣ`.
- `uniformizerUnitFactor_mul_uniformizer_zpow`, `exists_integerUnit_mul_uniformizer_zpow`: `x = u · ϖ^(v(x))` with `u ∈ 𝒪[K]ˣ`.
- Simp-style lemmas for products, inverses, quotients and powers, and for equality of classes in the quotient.

Exactness rests on `valuation_eq_one_of_valuationMap_eq_zero`: a unit of valuation zero has valuation one in the value group, hence lies in `𝒪[K]`.

## Watch for

- Sign convention: `valuationMap` sends a uniformizer of `𝒪[K]` to `−1`, not `+1` (the comment calls it the inverse-standard convention, used by the local Artin map of the library). The element `ϖ` with `valuationMap ϖ = 1` used in the decomposition `x = u · ϖ^(v(x))` is therefore the inverse of a uniformizer of `𝒪[K]`, and `v(x)` is minus the usual order of `x`.
- `valuationShortComplex` is not a short complex in Mathlib's sense; it is `valuationMap` itself. Exactness is stated as the range–kernel equality above, together with surjectivity.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`: the Lean file is the source byte for byte (SHA-256 `f61250f1612fab345fc98341c1de737e9be4cf763f31e374f6d21ad433695a4e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
