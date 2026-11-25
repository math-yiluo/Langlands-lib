# The norm on graded principal units is the residue trace

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Trace`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite unramified Galois extension L/K of nonarchimedean local fields and n ≥ 1, the file shows that the norm U_L^(n)/U_L^(n+1) → U_K^(n)/U_K^(n+1) becomes the trace 𝓀_L → 𝓀_K when both quotients are identified with the residue fields through the classes of 1 + r·π^n, π a chosen uniformizer of K (which stays a uniformizer of L). Since the trace of a finite extension of finite fields is surjective, so is the graded norm.

## Main definitions and results

Hypotheses: K : Type u, L : Type v nonarchimedean local fields, L/K finite, the valuation of L extending that of K (`Valuation.HasExtension`), `Module.Finite 𝒪[K] 𝒪[L]`, `IsUnramifiedValuedExtension K L`, and n ≥ 1; the statements about the norm also assume L/K Galois, `LocalFieldTheory.ValuativeExtension K L` and `IsIntegralClosure 𝒪[L] 𝒪[K] L`.

- `UnramifiedPrincipalUnits.quotientNorm_oneAdd_uniformizerPow_eq_trace`: for r ∈ 𝒪_L, the norm of the class of 1 + r·π^n, pushed back to the graded piece of L, corresponds to the trace of the residue of r.
- `principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_oneAdd_uniformizer_pow_eq_trace`: the same statement read on the graded piece of K, using injectivity of the map from the graded piece of K to that of L.
- `principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_trace_coord`: in residue coordinates, the graded norm is `Algebra.trace 𝓀[K] 𝓀[L]`.
- `principalUnitsSuccQuotTraceOfUnramifiedValuation K L n hn`: this trace model as an additive map between graded pieces, with a simp lemma, and `principalUnitsSuccQuotTraceOfUnramifiedValuation_surjective`.
- `principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_eq_trace`: the graded norm equals the trace model.
- `..._toAdditive_surjective` and `principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_surjective`: the graded norm is surjective.

## Proof

The norm of 1 + a is congruent to 1 + Σ_σ σ(a) modulo 𝔪_L^(n+1). For a = r·π^n with π in K, Σ_σ σ(a) = (Σ_σ σ(r))·π^n, and Σ_σ σ(r) reduces to the residue trace of r. Surjectivity comes from surjectivity of the residue trace (`residueField_trace_surjective_of_valuationExtension`).

## Caveats

The coordinates depend on the uniformizer `chosenIntegerRingUniformizer K`; the trace model is defined only with respect to it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Unramified/PrincipalUnits/Trace.lean`: the Lean file is the source byte for byte (SHA-256 `ed22027c18648876ae618df686f1ce96ef4523e2246ba6405c32d29ab2b11f82`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
