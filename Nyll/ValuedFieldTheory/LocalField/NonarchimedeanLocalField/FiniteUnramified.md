# Finite unramified extensions of local fields

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension `L/K` of nonarchimedean local fields (Mathlib's `IsNonarchimedeanLocalField`) whose valuation of `L` extends that of `K`, the file studies the unramified case. It shows that a uniformizer of `K` stays a uniformizer in `L`, compares the filtrations `𝓂ⁿ` and principal units `Uⁿ` of the two fields, and, for `L/K` Galois, identifies `Gal(L/K)` with the automorphism group of the residue extension and Galois sums with residue traces.

## Definitions

- `IsUnramifiedValuedExtension K L`: a class asserting that `𝓂[L]` has ramification index `1` over `𝒪[K]`.
- `maximalIdealPowMapOfUnramifiedValuation`, `maximalIdealPowSuccQuotMapOfUnramifiedValuation`: the maps `𝓂_Kⁿ → 𝓂_Lⁿ` and `𝓂_Kⁿ/𝓂_K^(n+1) → 𝓂_Lⁿ/𝓂_L^(n+1)`.
- `principalUnitsMapOfUnramifiedValuation`, `principalUnitsSuccQuotMapOfUnramifiedValuation`: the maps `U_Kⁿ → U_Lⁿ` and `U_Kⁿ/U_K^(n+1) → U_Lⁿ/U_L^(n+1)`.
- `galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure`: the isomorphism `Gal(L/K) ≃* Aut(𝓀[L]/𝓀[K])`.

## Results

- `unramifiedValuation_residue_finrank_eq_finrank`: `[𝓀[L] : 𝓀[K]] = [L : K]`, from `e · f = [L : K]` proved elsewhere.
- `maximalIdeal_map_eq_maximalIdeal_of_unramifiedValuation`: `𝓂_K 𝒪[L] = 𝓂_L`; hence the image of the chosen uniformizer of `K` is irreducible in `𝒪[L]`, and its normalized valuation in `L` is `-1` (that of its inverse is `1`).
- The maps on graded pieces commute with the identifications `𝓀 ≃ 𝓂ⁿ/𝓂^(n+1)` (every `n`) and `𝓀 ≃ Uⁿ/U^(n+1)` (`n ≥ 1`), with `L` using the image of the `K`-uniformizer. Consequently `principalUnitsSuccQuotMapOfUnramifiedValuation_injective` holds for `n ≥ 1`.
- `principalUnits_of_integerUnitsMap_mem_principalUnits_of_unramifiedValuation`: a unit of `𝒪[K]` lying in `U_Lⁿ` already lies in `U_Kⁿ`.
- For `L/K` Galois: `#Aut(𝓀[L]/𝓀[K]) = #Gal(L/K)`, the inertia subgroup is trivial, and the residue action `Gal(L/K) → Aut(𝓀[L]/𝓀[K])` is bijective.
- `galoisGroup_sum_residue_eq_algebraMap_trace_of_unramifiedValuation_of_isIntegralClosure`: the residue of `Σ_σ σ(a)` is the residue trace of the residue of `a`; `galoisSum_uniformizerGraded_eq_residueTrace` is the same statement on `𝓂_Lⁿ/𝓂_L^(n+1)`.

## Proofs

`𝓂_K 𝒪[L] = 𝓂_L` comes from Mathlib's factorization of `𝓂_K 𝒪[L]` into primes over `𝓂_K`, only `𝓂_L` occurring. Injectivity on graded pieces reduces to injectivity of the residue field map. Bijectivity of the residue action combines trivial kernel (ramification index one, an earlier library result) with equal cardinalities.

## Watch for

- Unramified means only `e = 1`; full residue degree is derived, not assumed.
- `Module.Finite 𝒪[K] 𝒪[L]` and, in the Galois part except the cardinality comparison, `IsIntegralClosure 𝒪[L] 𝒪[K] L` are typeclass hypotheses, not deduced here.
- The graded comparisons use the image of the `K`-uniformizer, not the uniformizer chosen for `L`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean`: the Lean file is the source byte for byte (SHA-256 `db60b3d7dd07ee94056592a162c604b87d435b34b29189d0023b3193b4f6d5d1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
