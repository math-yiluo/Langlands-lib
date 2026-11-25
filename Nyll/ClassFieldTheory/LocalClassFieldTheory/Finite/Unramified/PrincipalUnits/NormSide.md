# The norm of a unit as a product of Galois conjugates

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.NormSide`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension L/K of nonarchimedean local fields with 𝒪_L the integral closure of 𝒪_K, the file writes the norm of a unit u ∈ 𝒪_L^×, viewed back in 𝒪_L, as the product of the conjugates σ(u), and deduces that this "extension-side" norm preserves each principal unit group U_L^(n) = 1 + 𝔪_L^n and acts on the graded pieces U_L^(n)/U_L^(n+1).

## Main definitions and results

Typical hypotheses: K : Type u, L : Type v nonarchimedean local fields, L/K finite Galois, the valuation of L extending that of K (`Valuation.HasExtension` and `LocalFieldTheory.ValuativeExtension K L`), `IsIntegralClosure 𝒪[L] 𝒪[K] L`. The Galois group acts on 𝒪_L through the integral-closure identification.

- `normIntegerUnits_to_fieldUnits`: the norm on 𝒪_L^× agrees with the field norm on L^×.
- `integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure`: N(u), embedded in 𝒪_L^×, equals ∏_σ σ(u).
- `galoisGroup_prod_mem_principalUnits_of_isIntegralClosure` and `integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isIntegralClosure`: if u ∈ U_L^(n), then ∏_σ σ(u), hence the embedded norm, lies in U_L^(n).
- `principalUnitsNormExtensionSideOfIsIntegralClosure K L n : U_L^(n) →* U_L^(n)`, u ↦ N(u) seen in L, with `_apply` and `_eq_galoisGroup_prod`.
- `principalUnitsNormExtensionSideOfIsIntegralClosure_oneAdd_sub_one_sub_sum_mem_maximalIdeal_pow_succ`: for n ≥ 1 and a ∈ 𝔪_L^n, N(1 + a) − 1 − Σ_σ σ(a) ∈ 𝔪_L^(n+1).
- `principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure K L n`: the induced endomorphism of U_L^(n)/U_L^(n+1), with `_mk` and `_eq_galoisGroup_prod` (the product of the induced Galois actions).

## Caveats

- Although the file sits under `Unramified`, none of its statements assumes L/K unramified.
- The extension-side norm takes values in U_L^(n), not in U_K^(n); descending it to K is left to other files.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Unramified/PrincipalUnits/NormSide.lean`: the Lean file is the source byte for byte (SHA-256 `d6990d795834def3d2c7afc9eab55249e9e4b7471279f7e2eeba1a65684e1ae2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
