# Hensel factorization as an 𝔪-adic limit

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.WeakLimits`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file passes from the infinite sequence of Hensel approximants to an actual factorization, over a local ring `R` without zero divisors that is complete for the topology of its maximal ideal 𝔪. The approximants are the iterates g_n, h_n built from the correction sequences `henselFactorization_infinitePCorr_of_mem_span` and `henselFactorization_infiniteQCorr_of_mem_span` of the previous file, starting from an element π ≠ 0 of 𝔪.

## Common hypotheses

deg f ≤ d and m ≤ d; g0 has degree m and reduces to ḡ of degree m with nonzero leading coefficient; deg h0 ≤ d − m; an initial factorization f − g0·h0 = π·f1; and a Bezout relation a·g0 + b·h0 − 1 = π·e.

## Main results

- `henselFactorization_infiniteG_coeff_adicCoeffCauchy_of_mem_span` and the `infiniteH` analogue: for each i, the sequence of i-th coefficients of g_n (resp. h_n) is Cauchy for the 𝔪-adic filtration.
- `henselFactorization_exists_infiniteG_limitPolynomial_of_mem_span` and the `infiniteH` analogue: if R is 𝔪-adically precomplete (`IsPrecomplete`), there is G with deg G ≤ m (resp. H with deg H ≤ d − m) such that every coefficient of g_n − G lies in 𝔪^n.
- `henselFactorization_exists_limit_factorization_of_mem_span`: if moreover R is 𝔪-adically Hausdorff (`IsHausdorff`) and h0 reduces to h̄, there are G, H with deg G ≤ m, deg H ≤ d − m, f = G·H, and G, H reducing to ḡ, h̄.

## Proof

The coefficient Cauchy property comes from the estimate that, for M ≤ N, g_N − g_M has coefficients in 𝔪^(M+1). Limits are taken coefficientwise with a uniform degree bound, by lemmas of the file on adic limits. The identity f = G·H follows from the error estimate f − g_n·h_n ∈ 𝔪^(n+1) and the Hausdorff property; the reductions pass to the limit because every g_n is congruent to g0 modulo 𝔪.

## Points to watch

- No assumption 𝔪 ≤ (π) is made: π need not generate 𝔪. In exchange, the initial factorization and the Bezout relation are required with an explicit factor π, which is stronger than a congruence modulo 𝔪 unless π generates 𝔪.
- Completeness is 𝔪-adic, through Mathlib's `IsPrecomplete` and `IsHausdorff` for the maximal ideal; no valuation appears.
- The results give only degree upper bounds for G and H and do not state that G is monic.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Factorization/WeakLimits.lean`: the Lean file is the source byte for byte (SHA-256 `79ee7c45f58e6f92097f581e33f24634c56d083ef18ac048630629c1f665b4ac`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
