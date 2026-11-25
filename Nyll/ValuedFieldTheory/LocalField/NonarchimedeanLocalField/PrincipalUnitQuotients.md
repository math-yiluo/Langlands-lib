# Successive quotients of the principal-unit filtration

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a field with a valuative relation, `𝒪[K]` its valuation ring, `𝓂[K]` the maximal ideal and `U^n` the principal units, the units `u` of `𝒪[K]` with `u - 1 ∈ 𝓂^n` (so `U^n = 1 + 𝓂^n` for `n ≥ 1`). This file builds the quotients `U^n/U^(n+1)` and `𝓂^n/𝓂^(n+1)` and, for `n ≥ 1`, identifies them through `a ↦ 1 + a`. For a nonarchimedean local field it also proves that the filtrations are separated, relates them to the topology, and shows that infinite products of ever deeper principal units converge.

## Quotients and their comparison

- `PrincipalUnitsSuccQuot K n`: the commutative group `U^n/U^(n+1)`, with quotient map `principalUnitsSuccQuotMk`, lifting, induction, and exactness of `U^(n+1) → U^n → U^n/U^(n+1)` (`principalUnitsSuccIncl_exact`).
- `MaximalIdealPowSuccQuot K n`: the `𝒪[K]`-module `𝓂^n/𝓂^(n+1)`, with quotient map and lifts.
- `principalUnitOneAddOfMemPow`: for `n ≥ 1` and `a ∈ 𝓂^n`, the unit `1 + a`, also as an element of `U^n`.
- `finset_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ`: if all `aᵢ ∈ 𝓂^n` with `n ≥ 1`, then `∏ (1 + aᵢ) ≡ 1 + Σ aᵢ` modulo `𝓂^(n+1)`.
- `maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot`: for `n ≥ 1`, the additive isomorphism `𝓂^n/𝓂^(n+1) ≃ U^n/U^(n+1)` induced by `a ↦ 1 + a`; `maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot` is its multiplicative form, meant for the Herbrand quotient API.
## Results for a local field

- `maximalIdeal_iInf_pow_eq_bot`: `⋂ 𝓂^n = 0` (Krull intersection); hence `principalUnits_eq_one_of_mem_all`: a unit in every `U^n` is `1`.
- Every `𝓂^n` is closed and a neighbourhood of `0` in `𝒪[K]`, and every neighbourhood of `0` contains some `𝓂^N`. If units `f d` converge to a unit `x`, then eventually `f d / x ∈ U^n`.
- `principalUnitsCorrectionProduct K n z`: the partial products of a sequence with `z d ∈ U^(n+d)`. They stay in `U^n`, consecutive tails lie in `U^(n+m)`, and they form a Cauchy sequence (`principalUnitsCorrectionProduct_cauchySeq`). `exists_tendsto_principalUnitsCorrectionProduct_sub_one_mem` gives a limit `x ∈ 𝒪[K]` with `x - 1 ∈ 𝓂^n`, and for `n ≥ 1` `exists_tendsto_principalUnitsCorrectionProduct_principalUnit` places the limit in `U^n`.

## Points to watch

- The algebraic constructions need only `[Field K] [ValuativeRel K]`; the local-field hypothesis enters only in the separatedness, topological and limit statements.
- The convergence statements, except `tendsto_pow_succ_of_mem_maximalIdeal` and its signed variant (powers of `x ∈ 𝓂[K]` tend to `0`), assume a uniform structure on `K` compatible with addition (`[UniformSpace K] [IsUniformAddGroup K]`); completeness of `𝒪[K]` is supplied by an instance, not by a hypothesis.
- For `n = 0` the limit of the correction products is only obtained as an element of `𝒪[K]`, not as a unit; a comment calls the unit statement a later step, and the file supplies it only for `n ≥ 1`.
- The comparison with `𝓂^n/𝓂^(n+1)` requires `1 ≤ n`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`: the Lean file is the source byte for byte (SHA-256 `0095f2e54546cfee54d265945d8710444837c78307998681783bd83ad5af38cb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
