# Recursive Hensel iterates

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Iteration`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file defines the sequence of approximants used for each factor in Hensel's iteration, F_0 = F0 and F_(n+1) = F_n + π^(n+1)·c_(n+1) for a correction sequence c : ℕ → R[X], and proves the congruences and Cauchy-type coefficient estimates needed later to pass to a limit. Everything is over a commutative ring `R`, local where the maximal ideal 𝔪 appears.

## Definition

- `henselFactorization_henselIterate π F0 corr n`: the n-th iterate, with simp lemmas `henselFactorization_henselIterate_zero` and `henselFactorization_henselIterate_succ`. The value `corr 0` is never used.

## Main results

- `henselFactorization_henselIterate_span_singleton`: every iterate is coefficientwise congruent to F0 modulo (π), with no hypothesis on π; `henselFactorization_henselIterate_reduction_of_mem` gives the congruence modulo 𝔪 when π ∈ 𝔪.
- `henselFactorization_henselIterate_natDegree_le`: if F0 and all corrections have degree at most M, so do all iterates.
- Dependence on the corrections: the n-th iterate depends only on c_k for k ≤ n (`henselFactorization_henselIterate_eq_of_corr_eq_le`); changing c at an index k leaves the iterates of index below k unchanged, and setting c_(n+1) = c gives F_n + π^(n+1)·c (`henselFactorization_henselIterate_update_of_lt`, `henselFactorization_henselIterate_update_next`). Two further lemmas carry identities f − g_r·h_r = π^(r+1)·f_r through such an update, and one keeps a uniform degree bound on the corrections.
- Increments: F_(n+1) − F_n = C(π^(n+1))·c_(n+1), so its coefficients lie in (π^(n+1)), in (π)^(n+1), and in 𝔪^(n+1) when π ∈ 𝔪.
- Cauchy estimates: for m ≤ n, the coefficients of F_n − F_m lie in 𝔪^(m+1) when R is local and π ∈ 𝔪 (`henselFactorization_henselIterate_sub_coeff_mem_maximalIdeal_pow_of_le_of_mem`), and in (π)^(m+1) in any commutative ring (`henselFactorization_henselIterate_sub_coeff_mem_span_pow_of_le`).

## Proof

The congruences, the degree bound, the Cauchy estimates and the independence of an iterate from later corrections are proved by induction on the index, from the update lemmas of the single-step file and the factor-to-coefficient lemmas of the power-step file; the other statements follow by direct rewriting, without induction.

## Points to watch

- The indexing is shifted: at stage r the invariant used with these iterates is f − g_r·h_r = π^(r+1)·f_r, and the correction at stage n+1 is multiplied by π^(n+1).
- The estimates are purely algebraic; no convergence, completeness or limit appears in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Factorization/Iteration.lean`: the Lean file is the source byte for byte (SHA-256 `ee3c550ca4ed76ca5a609e127a723cf6a4a776175cfdc2ca99a6ed4f74ae3002`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
