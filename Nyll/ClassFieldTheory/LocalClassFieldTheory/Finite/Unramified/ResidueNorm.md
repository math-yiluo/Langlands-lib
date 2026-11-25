# The norm on units modulo first principal units

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.ResidueNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite unramified Galois extension L/K of nonarchimedean local fields, the file studies the norm on 𝒪^×/U^(1), which is the unit group of the residue field. It shows that the induced map 𝒪_L^×/U_L^(1) → 𝒪_K^×/U_K^(1) is the norm of the residue field extension 𝓀_L/𝓀_K, and hence is surjective.

## Main definitions and results

Hypotheses: K : Type u, L : Type v nonarchimedean local fields, L/K finite Galois, the valuation of L extending that of K (`Valuation.HasExtension` and `LocalFieldTheory.ValuativeExtension K L`), `IsIntegralClosure 𝒪[L] 𝒪[K] L`; for the quotient map also `Module.Finite 𝒪[K] 𝒪[L]` and `IsUnramifiedValuedExtension K L`.

- `integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L`: the norm induced on 𝒪^×/U^(1), with a simp lemma on classes; it is well defined because the norm maps U_L^(1) into U_K^(1).
- `residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_prod_of_isIntegralClosure` and its `AlgEquiv` form: the residue of N(u), viewed in 𝓀_L, is the product of the images of the residue of u under the residue automorphisms induced by Gal(L/K) (no unramified hypothesis).
- `integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_residue_algEquiv_base_extend`: the same on the quotient.
- `..._residue_base_extend_eq_residueNorm` and `integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_eq_residueNorm_of_unramifiedValuation`: the quotient norm equals the residue-field norm model `integerUnitsModPrincipalUnitsResidueNormOfValuationExtension`.
- `integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_surjective_of_unramifiedValuation`: the quotient norm is surjective.

## Proof

Unramifiedness is used to identify the product over Gal(L/K) of the induced residue automorphisms with the product over all automorphisms of 𝓀_L/𝓀_K. Surjectivity is then that of the norm of a finite extension of finite fields, supplied by the residue norm model.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Unramified/ResidueNorm.lean`: the Lean file is the source byte for byte (SHA-256 `3e4b968ec6bd382b717ca13d8beb4e6448d18ab07a86551bb26a5a12c9c38e32`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
