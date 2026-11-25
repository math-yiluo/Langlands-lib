# Norms in unramified extensions of local fields

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.Norm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite unramified extension L/K of nonarchimedean local fields, the file shows that the norm maps 𝒪_L^× onto 𝒪_K^×, computes the valuation of norms, and describes the norm subgroup: x ∈ K^× is a norm from L^× if and only if [L:K] divides its normalized valuation. The description is proved directly, by writing elements as norms.

## Main results

Typical hypotheses: K : Type u and L : Type v nonarchimedean local fields, L/K finite, the valuation of L extending that of K (both `Valuation.HasExtension` and `LocalFieldTheory.ValuativeExtension K L`), `Module.Finite 𝒪[K] 𝒪[L]`, `IsUnramifiedValuedExtension K L`; for the surjectivity statement, the converse implication and the final equivalence also L/K Galois, L with a uniform structure and `IsUniformAddGroup L`, and `IsIntegralClosure 𝒪[L] 𝒪[K] L`.

- `normIntegerUnits_surjective_unramified_of_isIntegralClosure`: the norm 𝒪_L^× → 𝒪_K^× is surjective. Proof: surjectivity on 𝒪^×/U^(1) (the residue-field norm) combined with surjectivity on the first principal units.
- `v_normUnits_integerUnitsToFieldUnits`: the norm of a unit of 𝒪_L has valuation 0.
- `v_normUnits_mapBase_inverseIntegerRingUniformizerFieldUnit_zpow` and `v_normUnits_integerUnit_mul_mapBase_inverseIntegerRingUniformizer_zpow`: for ϖ the chosen inverse uniformizer of K, v_K(N(u · ϖ^m)) = [L:K] · m.
- `v_normUnits_unramifiedValuation`: v_K(N x) = [L:K] · v_L(x) for all x ∈ L^×; ϖ is also a normalized generator in L because L/K is unramified, and x is decomposed as a unit times a power of ϖ.
- `finrank_dvd_valuation_of_mem_normSubgroup_unramified`: norms have valuation divisible by [L:K].
- `mem_normSubgroup_of_finrank_dvd_valuation_unramified_of_isIntegralClosure`: conversely, if [L:K] divides the valuation of x = u · ϖ^(m[L:K]), then x is the norm of ε · ϖ^m, where ε ∈ 𝒪_L^× has norm u.
- `mem_normSubgroup_unramifiedValuation_iff_finrank_dvd_valuation_of_isIntegralClosure`: the two directions combined.

## Caveats

- The extension of valuations enters through two separate instances, `Valuation.HasExtension` and `LocalFieldTheory.ValuativeExtension K L`.
- The valuation identities use the library's normalized valuation `v` and `valuationMap`, under which the chosen inverse uniformizer has value 1.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Unramified/Norm.lean`: the Lean file is the source byte for byte (SHA-256 `63ce37c817d24c1925c537d23a50164993e31cd3c3ae1d28281134a5ed263a90`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
