# Convergent products along the normal-basis filtration of units

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a nonarchimedean local field with chosen uniformizer `π`, `L/K` a finite Galois extension whose valuation extends that of `K`, `M` the normal-basis lattice and `Vⁿ = 1 + πⁿM` the corresponding set of units. The file shows that for large `n`, a product `z₀ z₁ z₂ ⋯` with `zᵢ ∈ Vⁿ⁺ⁱ` converges in `𝒪_L` to a unit in `Vⁿ`, and that norms and coboundaries commute with such limits. This is the analytic input of the successive-approximation argument for the local class-field axiom.

## Main results

- `chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_bound`: if `π^b M ⊆ 𝒪_L` and `b + 1 ≤ n`, then `Vⁿ⁺ⁱ` lies in the principal-unit group `U_L^(1+i)`; it rests on `chosenBaseUniformizerPow_integerRingFieldSubmodule_exists_mem_maximalIdeal_pow` (`π_K^m 𝒪_L ⊆ 𝓂_L^m`).
- `tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_bound`: under the same bound, `zᵢ ∈ Vⁿ⁺ⁱ` implies `zᵢ → 1` in `𝒪_L`.
- `continuous_integerRingEquiv_of_isNonarchimedeanLocalField`: every ring automorphism of `𝒪_L` is continuous.
- `tendsto_galoisGroupIntegerUnits_tateNorm_of_tendsto`, `tendsto_galoisGroupIntegerUnits_sigmaMinusOne_of_tendsto`: the norm `∏_σ σ(x)` and the coboundary `x ↦ g(x)/x` on `𝒪_Lˣ` commute with limits in `𝒪_L`, assuming `𝒪_L` is the integral closure of `𝒪_K` in `L`.
- `chosenNormalBasisPrincipalUnitCorrectionProduct z d`: the partial product of the first `d` terms of `z`. If `Vⁿ` is closed under multiplication it stays in `Vⁿ` (`_mem`); if every `Vᵏ` with `k ≥ n` is, the partial product at `m + d` divided by that at `m` lies in `Vⁿ⁺ᵐ` (`_div_mem`).
- `exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct_principalUnit`: if `π^b M ⊆ 𝒪_L` and `b + 1 ≤ n`, the partial products converge to an element of `U_L^(1)`.
- `chosenNormalBasisPrincipalUnitCorrectionProduct_limit_mem`: the limit lies in `Vⁿ` when `πⁿM` is closed and `Vⁿ` is closed under multiplication.
- `exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct`: assuming `𝒪_L` finite over `𝒪_K`, there is `c` such that for every `n ≥ c` and every sequence `zᵢ ∈ Vⁿ⁺ⁱ`, the partial products converge in `𝒪_L` to a unit `x ∈ Vⁿ`.

## Proofs

The final theorem takes `n` beyond three thresholds proved elsewhere: some `π^b M` lies in `𝒪_L`, `πⁿM` is multiplicatively closed, and `πⁿM` is closed. Convergence comes from the corresponding statement for ordinary principal units (`exists_tendsto_principalUnitsCorrectionProduct_principalUnit`), and membership of the limit from closedness. Continuity of Galois automorphisms of `𝒪_L` uses that ring automorphisms preserve the powers of the maximal ideal.

## Points to note

- Limits are taken in `𝒪_L`, not in a topology on the unit group.
- Several lemmas carry the multiplicative closure of `Vⁿ`, the closedness of `πⁿM` or the bound `π^b M ⊆ 𝒪_L` as explicit hypotheses; only the final theorem discharges them, for large `n`.
- The topological results assume `L` is a nonarchimedean local field with a uniform structure.
- `K` and `L` are taken in the same universe (`K L : Type u`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisInfiniteProduct.lean`: the Lean file is the source byte for byte (SHA-256 `462820479370264902e0f0ce605d6ee7996e4c79b49563168ceb6ba5790e8c55`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
