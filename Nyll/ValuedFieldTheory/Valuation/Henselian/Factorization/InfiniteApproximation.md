# Compatible Hensel prefixes and the infinite correction sequences

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.InfiniteApproximation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file turns the one-step extension of a finite Hensel prefix into a recursively chosen, compatible family of prefixes, and extracts from it two infinite correction sequences whose iterates g_N, h_N approximate a factorization f = g·h to every order. The limit itself is taken in later files. Except for the state structure and its stage-0 state (any π in a commutative local ring), `R` is a local ring without zero divisors, π ≠ 0 lies in the maximal ideal 𝔪, and m, d are degrees.

## Common hypotheses

deg f ≤ d and m ≤ d; g0 has degree m and reduces to ḡ of degree m with nonzero leading coefficient; deg h0 ≤ d − m; an initial factorization f − g0·h0 = π·f1; and a Bezout relation a·g0 + b·h0 − 1 = π·e.

## Definitions

- `HenselFactorizationFinitePrefixState π f g0 h0 m d N`: a structure holding correction sequences `pCorr`, `qCorr` and an error `fErr`, with the invariants that f − g_r·h_r is a multiple of π^(r+1) for all r ≤ N, all corrections have degrees at most m and d − m, f − g_N·h_N = π^(N+1)·fErr, g_N and h_N have degrees at most m and d − m, and g_N, h_N are congruent to g0, h0 modulo 𝔪.
- `henselFactorization_initialPrefixState_of_factor`: the stage-0 state, with zero corrections and error f1.
- `henselFactorization_chosenNextPrefixState_of_mem_span`: a stage-(N+1) state obtained from a stage-N state by a choice of one more correction, changing the corrections only at index N+1.
- `henselFactorization_prefixStateSeq_of_mem_span`: the recursively chosen sequence of states.
- `henselFactorization_infinitePCorr_of_mem_span`, `henselFactorization_infiniteQCorr_of_mem_span`: the diagonal sequences, whose n-th term is the n-th correction of the n-th state.

## Main results

- Coherence: the corrections of the N-th state at an index M ≤ N agree with those of the M-th state, hence with the infinite sequences.
- `henselFactorization_infiniteCorr_factor_prefix_of_mem_span`: for every N, f − g_N·h_N = π^(N+1)·f_N for some f_N, where g_N, h_N are the iterates built from g0, h0 and the infinite sequences; consequently its coefficients lie in 𝔪^(N+1).
- Degree bounds deg g_N ≤ m and deg h_N ≤ d − m, congruence of g_N, h_N with g0, h0 modulo 𝔪, and the Cauchy estimate that g_N − g_M and h_N − h_M have coefficients in 𝔪^(M+1) for M ≤ N.

## Proof

The next state is chosen with `Classical.choose` from the finite one-step extension. Coherence is proved by induction on N.

## Points to watch

- The initial factorization and the Bezout relation are needed with an explicit factor π, not only modulo 𝔪; 𝔪 need not equal (π).
- No completeness is used here; the iterates only form Cauchy sequences.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Factorization/InfiniteApproximation.lean`: the Lean file is the source byte for byte (SHA-256 `9ca8d5a465a1f8a7ce5ab4dc57399e352098e97417b45c2e33cb5ff45ff70285`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
