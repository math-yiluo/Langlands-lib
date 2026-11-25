# Norm estimates for finite separable totally ramified extensions

Module `FontaineWintenberger.FieldOfNorms.Estimates.NormEstimates`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy the library's class `IsPerfectResidueLocalField`, with residue characteristic `p`, and let `L/K` be finite separable, totally ramified (ramification index equal to `[L : K]`), of degree `p ^ n > 1`. Normality is not assumed. Write `S` for `spectralIntegerRing K L` and `N` for `Algebra.intNorm 𝒪[K] S`.

- `exists_intNorm_add_congruence_of_totallyRamified`: there is a real `b ≥ 0` with `apfRamificationBound K L = b` such that `N(x + y) − N(x) − N(y)` lies in the power `⌈(p − 1)/p · b⌉` of the maximal ideal of `𝒪[K]`, for all `x`, `y`.
- `exists_intNorm_estimates_of_totallyRamified`: moreover every `a` in `𝒪[K]` is congruent to some `N(α)` modulo the same power.
- `exists_intNorm_add_congruence_of_totallyRamified_intermediateField`: the additive estimate for an intermediate field of a finite Galois `Ω/K`.

The intermediate-field form reduces to the fixed-field estimate of the file on tame descent; the general form embeds `L` in a normal closure. Approximate surjectivity is `extensionValuationSubring_exists_intNorm_sub_mem_maximalIdeal_pow`.

The trivial extension is excluded (`hdegree`).

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Estimates/NormEstimates.lean` (SHA-256 of the source file `c2ed571d7dbe55e32572a8eeac7cc4b44901339c30cc2fea794d2757f602dd98`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
