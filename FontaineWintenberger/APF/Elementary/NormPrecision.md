# Additivity of the norm up to a precision, in prime degree

Module `FontaineWintenberger.APF.Elementary.NormPrecision`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field and `L/K` a totally ramified finite Galois extension of prime degree `p`. Write `S = spectralIntegerRing K L`, `N` for the integral norm `Algebra.intNorm 𝒪[K] S` and `𝔪_K` for the maximal ideal of `𝒪[K]`.

- `spectralIntegerRing_prime_degree_norm_add_congruence`: there is a natural number `t` with `apfRamificationBound K L = t` such that `N(α + β) - N α - N β ∈ 𝔪_K^⌊(p - 1)(t + 1) / p⌋` for all `α, β` in `S`.
- `spectralIntegerRing_prime_norm_add_congruence_of_bound`: for every real `b ≤ apfRamificationBound K L`, `N(x + y) - N x - N y ∈ 𝔪_K^⌈(p - 1) b / p⌉`.
- `mul_div_le_prime_norm_precision`, `ceil_mul_div_le_prime_norm_precision`: the inequalities between the exponents.

The first statement uses `spectralIntegerRing_prime_degree_ramification` and a trace-ideal estimate.

To watch for: total ramification is the hypothesis `he`. The ceiling is the natural-number ceiling, so the exponent is `0` for negative `b`.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Elementary/NormPrecision.lean` (SHA-256 of the source file `56641c96dd75694faeaaa586f0ea29905d31edbf8a206f0716b9cd41e408dae6`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
