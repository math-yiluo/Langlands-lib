# One-step lifting along the normal-basis filtration of units

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGradedLifting`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a nonarchimedean local field with chosen uniformizer `π`, `L/K` a finite Galois extension whose valuation extends that of `K`, with `𝒪_L` the integral closure of `𝒪_K`. Let `M` be the normal-basis lattice and `Vⁿ = 1 + πⁿM` the corresponding set of units. The file proves the single steps of the successive-approximation argument: at deep levels, a fixed unit is a norm up to a deeper fixed unit, and a unit of norm one is a coboundary up to a deeper unit of norm one.

## Main results

- `chosenNormalBasisPrincipalUnitLatticeClass_galoisGroup`: the class of `u − 1` in the graded lattice piece `πⁿM / πⁿ⁺¹M` depends equivariantly on `u ∈ Vⁿ`.
- `chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction`: the Galois action on the quotient `Vⁿ/Vⁿ⁺¹`, for subgroups with carriers `Vⁿ ⊇ Vⁿ⁺¹`.
- `chosenNormalBasisPrincipalUnitSuccQuotMulEquiv_galoisGroup`: every isomorphism `Φ` from `Vⁿ/Vⁿ⁺¹` to the multiplicative copy of `πⁿM / πⁿ⁺¹M` sending the class of `u` to the class of `u − 1` is Galois-equivariant.
- `exists_chosenNormalBasisPrincipalUnit_h0_oneStep_lifting`: there is `c` such that for `k ≥ c`, every Galois-fixed `a ∈ Vᵏ` can be written `a = N(b) · a'` with `b ∈ Vᵏ` and `a' ∈ Vᵏ⁺¹` fixed, `N` the norm (product over `Gal(L/K)`).
- `exists_chosenNormalBasisPrincipalUnit_hMinusOne_oneStep_lifting`: for a generator `g` of `Gal(L/K)`, there is `c` such that for `k ≥ c`, every `a ∈ Vᵏ` of norm 1 can be written `a = sigmaMinusOne g b · a'`, that is `(g(b)/b) · a'`, with `b ∈ Vᵏ` and `a' ∈ Vᵏ⁺¹` of norm 1.

The two lifting results also assume that `L` is a nonarchimedean local field and that `𝒪_L` is a finite `𝒪_K`-module.

## Proofs

For `k` beyond the threshold, `exists_chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot` provides subgroups with carriers `Vᵏ`, `Vᵏ⁺¹` and an isomorphism `Φ` as above. The class of `a` is carried by `Φ` to the graded lattice piece, where the Herbrand groups vanish (`chosenNormalBasisLatticeSuccQuot_herbrandH0_subsingleton`, `chosenNormalBasisLatticeSuccQuot_herbrandHMinusOne_subsingleton`). A preimage of the resulting norm or coboundary is pulled back through `Φ` to some `b ∈ Vᵏ`, and `a'` is `a / N(b)` or `a / (g(b)/b)`, which lies in `Vᵏ⁺¹`.

## Points to note

The sets `Vⁿ` are not subgroups by definition: the quotient action and the equivariance statement take subgroups whose carriers equal them, and the actions depend on these carrier equations; the two lifting theorems are stated for units of the sets themselves. The thresholds `c` are not explicit. `K` and `L` are taken in the same universe.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGradedLifting.lean`: the Lean file is the source byte for byte (SHA-256 `cdf794b523acde04073e7298f4d1c4d7194b136175676377dadad1b0c678b6a6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
