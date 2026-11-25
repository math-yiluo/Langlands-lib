# Ramification of totally ramified extensions of prime degree

Module `FontaineWintenberger.APF.Elementary.PrimeDegree`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field. For a totally ramified extension `L/K` of prime degree `n`, the file finds a single break, which determines the first ramification bound, the different, the trace ideal, the index `apfIndex K L` and `ψ = apfPsi K L`, `φ = apfPhi K L`.

## Galois case

For `L/K` finite Galois, with `S = spectralIntegerRing K L`:

- `spectralIntegerRing_exists_common_break_of_prime_degree`: there is a natural number `t` with `ramificationOrder g = t + 1` for every `g ≠ 1`.
- Given such `t`: `apfRamificationBound_eq_common_break` (the bound equals `t`), `spectralIntegerRing_different_order_of_common_order` (the different has exponent `(n - 1)(t + 1)`), `spectralIntegerRing_intTraceIdeal_of_common_break` (the trace of `S` is the power `⌊(n - 1)(t + 1) / n⌋` of the maximal ideal of `𝒪[K]`), `spectralIntegerRing_intTrace_order_bound`.
- `spectralIntegerRing_prime_degree_ramification` collects these; `spectralIntegerRing_prime_degree_norm_estimate` adds `(n - 1) t ≤ n · v(N(α + β) - N α - N β)` for the integral norm `N`.

## Separable case, not necessarily normal

- `apfIndex_prime_degree_different_profile`: for `L/K` finite separable, totally ramified of prime degree, there is a real `b ≥ 0` such that, for `u ≥ 0`, `apfIndex K L u` is `1` if `u ≤ b` and `n` otherwise, and the different of `S` has exponent `(n - 1)(b + 1)`.
- `apf_prime_degree_different_profile` adds `ψ(u) = b + n (u - b)` and `φ(v) = b + (v - b) / n` beyond `b`, both the identity up to `b`; `apfIndex_prime_degree_eq_different` gives `b` as the exponent of the different divided by `n - 1`, minus `1`.
- Versions for an intermediate field of a finite Galois extension: `intermediate_apfIndex_prime_degree_different_profile`, `apfIndex_prime_degree_different_profile_of_finiteGaloisIntermediateField`.
- `apfPsi_eq_of_index_profile`, `apfPhi_eq_of_index_profile`: any finite separable extension whose index has one step at `b ≥ 0`, from `1` to the degree, has these piecewise affine `ψ` and `φ`.

## Invariance lemmas

The ramification index and the exponent of the different are invariant under `K`-isomorphism (`spectral_ramificationIdx_algEquiv`, `spectral_different_order_algEquiv`) and do not depend on the valuation of `L` extending that of `K` (`extensionValuationSubring_ramificationIdx_eq_spectral`, `extensionValuationSubring_different_order_eq_spectral`).

## Proofs

A group of prime order has no proper nontrivial subgroup, so the lower ramification filtration has one break; the exponent of the different is the sum of `ramificationOrder` over nonidentity elements (called Hilbert's formula in the file). The nonnormal case passes to the normal closure.

## What to watch for

- Total ramification is the hypothesis `he`: the ramification index of the maximal ideal of the integer ring over `𝒪[K]` equals the degree. Primality is `hp`.
- The two results on index profiles do not assume a perfect residue field.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Elementary/PrimeDegree.lean` (SHA-256 of the source file `0579d2acea22ec79fc717bc62851f7991478528972bceb6d88dae6b6294c01b5`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
