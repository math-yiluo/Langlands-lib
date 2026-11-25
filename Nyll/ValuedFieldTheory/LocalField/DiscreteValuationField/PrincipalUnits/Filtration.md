# The higher principal unit groups U^n of a complete DVF

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field with a chosen complete discrete valuation (the library's `CompleteDVF`), valuation ring O, maximal ideal 𝔪 and residue field k, the file defines the higher principal unit groups U^n = { u ∈ O^* : u − 1 ∈ 𝔪^n } and proves their basic properties: the filtration is decreasing, U¹ is the kernel of reduction to k^*, and p-th powers push U^n into U^(n+1) for n ≥ 1 when k has characteristic p.

## Main definitions and results

- `higherPrincipalUnitGroup F n`: the subgroup U^n of O^*, with `mem_iff` unfolding membership. `antitone`: U^n ⊆ U^m for m ≤ n. `zero_eq_top`: U^0 is all of O^*.
- `residueUnitHom F`: the reduction homomorphism O^* → k^*. `mem_one_iff_residue_eq_one` and `residueUnitHom_eq_one_iff`: u ∈ U¹ iff its residue is 1; `residueUnitHom_eq_iff_residue_eq` compares two units.
- `one_add_pow_prime_sub_one_mem_pow_succ`: in any commutative ring with ideal I, if p is prime, p ∈ I, n ≥ 1 and a ∈ I^n, then (1 + a)^p − 1 ∈ I^(n+1).
- `natCast_mem_maximalIdeal_of_residue_ringChar_eq`: if k has ring characteristic p, then p ∈ 𝔪.
- `pow_mem_succ_of_natCast_mem_maximalIdeal` and `pow_mem_succ_of_residue_ringChar_eq`: for p prime with p ∈ 𝔪 (respectively char k = p) and n ≥ 1, u ∈ U^n implies u^p ∈ U^(n+1).

## Proofs

The binomial lemma writes (1 + a)^p = 1 + a^p + p·a·r and observes that a^p ∈ I^(np) ⊆ I^(n+1) and p·a ∈ I^(n+1).

## Points to note

- The module docstring says the file builds the library's `AntitoneSubgroupFiltration`; that packaging is not in this file.
- The p-th power statement is the coarse one (one step deeper); it does not give the sharper behaviour of p-th powers at high levels.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Filtration.lean`: the Lean file is the source byte for byte (SHA-256 `fbbf9e308784fe166c5a550449c211b6bba58650bf63bb21e0bdb4db7487402e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
