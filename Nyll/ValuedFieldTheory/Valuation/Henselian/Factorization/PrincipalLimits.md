# Hensel factorization as a π-adic limit

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.PrincipalLimits`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file passes from the infinite sequence of Hensel approximants to an actual factorization using the filtration by the powers of the principal ideal (π), rather than the powers of the maximal ideal 𝔪. Here `R` is a local ring without zero divisors and π ≠ 0 lies in 𝔪. According to the module comment, this is the route needed for complete valued fields whose maximal ideal is not assumed principal or adically separated. The approximants g_n, h_n are the iterates built from the correction sequences `henselFactorization_infinitePCorr_of_mem_span` and `henselFactorization_infiniteQCorr_of_mem_span` of the previous file.

## Common hypotheses

deg f ≤ d and m ≤ d; g0 has degree m and reduces to ḡ of degree m with nonzero leading coefficient; deg h0 ≤ d − m; an initial factorization f − g0·h0 = π·f1; and a Bezout relation a·g0 + b·h0 − 1 = π·e.

## Main results

- `henselFactorization_infiniteG_coeff_spanAdicCoeffCauchy_of_mem_span` and the `infiniteH` analogue: for each i, the i-th coefficients of g_n (resp. h_n) form a Cauchy sequence for the (π)-adic filtration.
- `henselFactorization_exists_infiniteG_spanLimitPolynomial_of_mem_span` and the `infiniteH` analogue: if R is (π)-adically precomplete, there is G with deg G ≤ m (resp. H with deg H ≤ d − m) such that every coefficient of g_n − G lies in (π)^n.
- `henselFactorization_infiniteCorr_error_coeff_mem_span_pow_of_mem_span`: every coefficient of f − g_N·h_N lies in (π)^(N+1).
- `henselFactorization_exists_limit_factorization_of_mem_span_principal`: if R is (π)-adically precomplete and Hausdorff and h0 reduces to h̄, there are G, H with deg G ≤ m, deg H ≤ d − m, f = G·H, and G, H reducing to ḡ, h̄ in the residue field.

## Proof

The Cauchy property is the estimate that, for M ≤ N, g_N − g_M has coefficients in (π)^(M+1), from the file on recursive iterates. Coefficientwise limits with a uniform degree bound come from the file on adic limits; f = G·H follows from the error estimate and the Hausdorff property. The limits are congruent to g0, h0 modulo (π), hence modulo 𝔪 since π ∈ 𝔪.

## Points to watch

- Completeness is assumed for the (π)-adic topology, through Mathlib's `IsPrecomplete` and `IsHausdorff` for `Ideal.span {π}`; nothing is assumed about 𝔪-adic completeness, and 𝔪 need not equal (π).
- The initial factorization and the Bezout relation are required with an explicit factor π, not only modulo 𝔪.
- Only upper bounds on the degrees of G and H are stated; G is not stated to be monic.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Factorization/PrincipalLimits.lean`: the Lean file is the source byte for byte (SHA-256 `8f6754a0373720500af0aed4230d8c9f3c61a3c265a4a94bf2564fa6381a878d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
