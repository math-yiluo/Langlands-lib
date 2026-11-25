# The norm on principal units of an unramified extension

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Basic`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite unramified Galois extension L/K of nonarchimedean local fields, the file restricts the norm 𝒪_L^× → 𝒪_K^× to the principal unit groups U^(n) = 1 + 𝔪^n and to the successive quotients U^(n)/U^(n+1), and computes the norm of 1 + a modulo 𝔪_L^(n+1) as 1 + Σ_σ σ(a). This is the preparation for identifying the graded norm with the residue trace, which is not done here.

## Main definitions and results

Hypotheses throughout: K : Type u and L : Type v nonarchimedean local fields, L/K finite Galois, the valuation of L extending that of K (`Valuation.HasExtension` and `LocalFieldTheory.ValuativeExtension K L`), `IsIntegralClosure 𝒪[L] 𝒪[K] L`, `Module.Finite 𝒪[K] 𝒪[L]`, `IsUnramifiedValuedExtension K L`.

- `normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure`: the norm maps U_L^(n) into U_K^(n), for every n.
- `principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n : U_L^(n) →* U_K^(n)`, the restricted norm, with a simp lemma; `principalUnitsMap_normOfUnramifiedValuationOfIsIntegralClosure_eq_normExtensionSide`: viewed back in L, it is the product of the Galois conjugates.
- `UnramifiedPrincipalUnits.norm_oneAdd_sub_galoisSum_mem_next`: for n ≥ 1 and a ∈ 𝔪_L^n, N(1 + a) − 1 − Σ_σ σ(a) lies in 𝔪_L^(n+1).
- `principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n`: the induced map U_L^(n)/U_L^(n+1) → U_K^(n)/U_K^(n+1), with a simp lemma on classes.
- `principalUnitsSuccQuotMap_normOfUnramifiedValuationOfIsIntegralClosure_oneAdd_base_eq_sum`: mapped back to the graded piece of L, the norm of the class of 1 + a is the class of 1 + Σ_σ σ(a).

## Caveats

The congruence statements are for n ≥ 1, and they are read in 𝒪_L after pushing the base-field quotient into the extension (`principalUnitsMapOfUnramifiedValuation`, `principalUnitsSuccQuotMapOfUnramifiedValuation`), not directly in K.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Unramified/PrincipalUnits/Basic.lean`: the Lean file is the source byte for byte (SHA-256 `eb40d967d2124712820d664fc38cb26b6b36915c3e74201f4dcb1f2cbb4cb905`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
