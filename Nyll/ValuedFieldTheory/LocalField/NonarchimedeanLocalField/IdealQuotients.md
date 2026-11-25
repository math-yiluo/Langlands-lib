# Successive quotients of the maximal ideal and of the principal units

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field `K` with valuation ring `𝒪[K]`, maximal ideal `𝓂[K]` and residue field `𝓀[K]`, this file fixes a uniformizer, computes its normalized valuation, and identifies the successive quotients `𝓂^n/𝓂^(n+1)` and, for `n ≥ 1`, `U^n/U^(n+1)` with the residue field. It deduces that these quotients are finite with as many elements as `𝓀[K]`.

## Main definitions and results

- `chosenIntegerRingUniformizer K`: an irreducible element of `𝒪[K]` picked by choice; `chosenIntegerRingUniformizer_maximalIdeal_eq` says it generates `𝓂[K]`. `integerRingUniformizerFieldUnit` and `inverseIntegerRingUniformizerFieldUnit` are it and its inverse as units of `K`.
- `valueGroupWithZeroIsoInt_of_integerRing_irreducible`: for every irreducible `ϖ` of `𝒪[K]`, the normalized valuation sends `ϖ` to `ofAdd (-1)`. Hence `v_integerRingIrreducibleFieldUnit` (value `-1`) and its `_inv` form (value `1`), with versions for the chosen uniformizer.
- `exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRing`: for every `x : K` some `ϖ^n · x` lies in `𝒪[K]`.
- `maximalIdeal_pow_eq_span_uniformizer_pow`: `𝓂^n = (ϖ^n)`.
- `residueLinearEquivMaximalIdealPowSuccQuotOfIrreducible`: for irreducible `ϖ`, the `𝒪[K]`-linear isomorphism `𝓀[K] ≃ 𝓂^n/𝓂^(n+1)` induced by `r ↦ r·ϖ^n`; the `chosenResidue...` versions use the chosen uniformizer. The instance `maximalIdealPowSuccQuot_finite` and `maximalIdealPowSuccQuot_card_eq_residue` follow.
- `principalUnitsSuccQuotAddEquivResidue` and `principalUnitsSuccQuotAddEquivResidueOfIrreducible`: for `n ≥ 1`, an additive isomorphism `U^n/U^(n+1) ≃ 𝓀[K]`.
- `principalUnitsSuccQuotUniformizerCoord`: the class of `1 + r·ϖ^n` in `U^n/U^(n+1)`. It turns sums of `r` into products, every class has this form, two such classes agree exactly when the residues of the coefficients agree, and a class is trivial exactly when `r ∈ 𝓂[K]`.
- `finite_principalUnitsSuccQuot` and `principalUnitsSuccQuot_card_eq_residue`: `U^n/U^(n+1)` is finite with `#𝓀[K]` elements.

Small lemmas identify `𝒪[K]/𝓂[K]` with `𝓀[K]` (definitionally) and compute the maps on representatives.

## Proofs

Since `𝓂 = (ϖ)`, the value of `ϖ` is the largest value below `1`, which the order isomorphism to `ℤₘ₀` sends to `ofAdd (-1)`. The isomorphism `𝓀 ≃ 𝓂^n/𝓂^(n+1)` is the first isomorphism theorem for `r ↦ [r·ϖ^n]`, whose kernel is `𝓂`. The unit statements compose it with the isomorphism `𝓂^n/𝓂^(n+1) ≃ U^n/U^(n+1)` (`maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot`) from the imported file on principal-unit quotients.

## Points to watch

- Sign convention: the library's additive valuation `IsNonarchimedeanLocalField.v` gives a uniformizer the value `-1` and its inverse the value `1`; the comments call the inverse the positive uniformizer.
- The uniformizer is a choice. The `...OfIrreducible` variants take an explicit irreducible `ϖ`, for comparisons across extensions.
- `principalUnitsSuccQuot_card_eq_residue` takes a `Finite` instance as argument; `finite_principalUnitsSuccQuot` supplies it.
- All statements about `U^n/U^(n+1)` require `1 ≤ n`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean`: the Lean file is the source byte for byte (SHA-256 `ef7b0c8d6f47f2088ab20119a0a7dacab1d1a07ecc74a346bb00213e475bec48`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
