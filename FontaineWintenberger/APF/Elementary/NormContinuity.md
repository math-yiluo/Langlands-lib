# Continuity of the norm in a totally ramified Galois extension of prime degree

Module `FontaineWintenberger.APF.Elementary.NormContinuity`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field and `L/K` a totally ramified finite Galois extension of prime degree `p`. Write `S = spectralIntegerRing K L`, `N` for the integral norm `Algebra.intNorm 𝒪[K] S`, and `𝔪_S`, `𝔪_K` for the maximal ideals.

- `exists_spectralIntegerRing_prime_norm_sub_precision`: there is a natural number `t` with `apfRamificationBound K L = t`, the different has exponent `(p - 1)(t + 1)`, and `x - y ∈ 𝔪_S^r` implies `N x - N y ∈ 𝔪_K^m`, `m = min(r, ⌊((p - 1)(t + 1) + r) / p⌋)`.
- `spectralIntegerRing_prime_norm_sub_congruence`: `x - y ∈ 𝔪_S^r` implies `N x - N y ∈ 𝔪_K^⌈φ(r)⌉`, with `φ = apfPhi K L`.
- `ceil_prime_herbrand_piece_le_precision`: the inequality between the two exponents.

The proofs use the description of ramification in prime degree and a trace-ideal estimate, from other modules.

To watch for: total ramification is the hypothesis `he`, primality `hp`.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Elementary/NormContinuity.lean` (SHA-256 of the source file `d29837aa69fb86ae06e9f6258e6bee4afa13c6f4573c694cd3b177d3fcf8a171`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
