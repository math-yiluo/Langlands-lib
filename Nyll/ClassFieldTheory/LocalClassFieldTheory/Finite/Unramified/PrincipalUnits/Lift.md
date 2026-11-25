# Surjectivity of the norm on principal units of an unramified extension

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Lift`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite unramified Galois extension L/K of nonarchimedean local fields, the file proves that the norm maps U_L^(n) onto U_K^(n) for every n ≥ 1, where U^(n) = 1 + 𝔪^n. The proof is the classical successive approximation: surjectivity on each graded piece U^(n)/U^(n+1) is lifted to the whole group by a convergent product.

## Main result

`principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_surjective`: let K : Type u and L : Type v be nonarchimedean local fields, L with a uniform structure and `IsUniformAddGroup L`, L/K finite Galois, the valuation of L extending that of K (`Valuation.HasExtension` and `LocalFieldTheory.ValuativeExtension K L`), `IsIntegralClosure 𝒪[L] 𝒪[K] L`, `Module.Finite 𝒪[K] 𝒪[L]`, `IsUnramifiedValuedExtension K L`. Then for n ≥ 1 the restricted norm U_L^(n) → U_K^(n) is surjective.

## Steps

- `principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_lift_mod_succ` and `..._div_lift_mem_succ`: every y ∈ U_K^(n) is a norm modulo U_K^(n+1), from surjectivity of the norm on graded pieces.
- `..._approx_mem_add`: for every d, some x ∈ U_L^(n) has y / N(x) ∈ U_K^(n+d).
- `principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState`: a coherent sequence of such approximations, built recursively with corrections chosen by `Classical.choose`; consecutive terms differ by an element of U_L^(n+d), and the sequence is the partial product of the corrections.
- `exists_tendsto_principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState`: the sequence converges in 𝒪_L to an element of U_L^(n), by the convergence of products of corrections of increasing depth.
- `eventually_normIntegerUnits_div_mem_principalUnits_of_tendsto_units_of_isIntegralClosure`: a continuity statement for the norm, derived from multiplicativity and preservation of the levels U^(n).
- `..._limit_error_mem_add_all` and `..._eq_of_error_mem_add_all`: the error at the limit lies in every U_K^(n+d), hence is 1.

## Caveats

- The statement is for n ≥ 1 only.
- Convergence uses the uniform structure on L; it is an explicit hypothesis of the limit steps and of the main theorem.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Unramified/PrincipalUnits/Lift.lean`: the Lean file is the source byte for byte (SHA-256 `ec94eb4a2cb9fef5761b550368cb6528002e2c5aa9cd9a7f91a0a9ce4861e74e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
