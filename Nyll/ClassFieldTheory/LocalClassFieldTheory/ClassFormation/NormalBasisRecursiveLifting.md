# Norms and coboundaries on deep normal-basis units

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisRecursiveLifting`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of nonarchimedean local fields, the valuation of `L` extending that of `K`, with `𝒪_L` the integral closure of `𝒪_K` and finite over it. Let `M` be the normal-basis lattice, `π` the chosen uniformizer of `K` and `Vⁿ = 1 + πⁿM`. The file iterates the one-step graded lifting and passes to the limit, showing that at deep levels every fixed unit of `Vⁿ` is a norm, and every unit of norm one a coboundary, from `Vⁿ` itself.

## Main results

- `exists_chosenNormalBasisPrincipalUnit_fixed_is_tateNorm`: there is `c` such that for every `n ≥ c`, every `a ∈ Vⁿ` fixed by `Gal(L/K)` equals `N(b) = ∏_σ σ(b)` for some `b ∈ Vⁿ`.
- `exists_chosenNormalBasisPrincipalUnit_normOne_is_sigmaMinusOne`: for a generator `g` of `Gal(L/K)`, there is `c` such that for every `n ≥ c`, every `a ∈ Vⁿ` with `N(a) = 1` equals `sigmaMinusOne g b`, that is `g(b)/b`, for some `b ∈ Vⁿ`.

## Proofs

The one-step lifting results (`exists_chosenNormalBasisPrincipalUnit_h0_oneStep_lifting` and its degree −1 analogue) are fed into the dependent-choice construction `chosenFilteredLiftStateSequence`, with `F` the norm or the coboundary map. This gives corrections `zᵢ ∈ Vⁿ⁺ⁱ` and remainders in `Vⁿ⁺ⁱ` such that, for every `d`, `a` is `F` of the product of the first `d` corrections times the `d`-th remainder. For `n` beyond the thresholds, the partial products converge to some `x ∈ Vⁿ` (`exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct`), the remainders tend to 1, and `F` commutes with the limit, so `a = F(x)`.

## Points to note

The thresholds are not explicit; they combine those of the one-step lifting, of the convergence of products, and a bound `π^b M ⊆ 𝒪_L`. Limits are taken in `𝒪_L`. The degree −1 statement is relative to the chosen generator `g`. `K` and `L` are taken in the same universe, and `L` carries a `UniformSpace` structure with `IsUniformAddGroup`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisRecursiveLifting.lean`: the Lean file is the source byte for byte (SHA-256 `a61a0d7dd9472f15daa499a56b8d386df3c94fadc80b844d9e8a932802709b6e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
