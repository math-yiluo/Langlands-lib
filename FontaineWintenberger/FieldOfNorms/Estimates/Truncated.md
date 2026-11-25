# Truncated norms between quotients of integer rings

Module `FontaineWintenberger.FieldOfNorms.Estimates.Truncated`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy the library's class `IsPerfectResidueLocalField`, with residue characteristic `p`, let `L/K` be separable, and let `E ≤ F` be finite intermediate fields with `F/E` totally ramified of degree `p ^ d`. The integral norm `integerNorm E F` is multiplicative but not additive. The file shows that, modulo a power of the maximal ideal controlled by the ramification bound of `F/E`, it becomes a surjective ring homomorphism between quotients of the integer rings.

## Definitions

- `truncatedAddVal R r`: for a discrete valuation ring `R`, the function on `R ⧸ 𝔪 ^ r` sending the class of `x` to `min (addVal x) r`, with values in `ℕ∞`.
- `FiniteIntermediateField.truncatedNorm E F hEF d b he hd hb r s hrs hrb`: the ring homomorphism from the integers of `F` modulo the `s`-th power of the maximal ideal to the integers of `E` modulo the `r`-th power, induced by `integerNorm`. It needs `r ≤ s` and `r ≤ ⌈(p − 1)/p · b⌉`, where `b` is a real number with `b ≤ apfRamificationBound E F`.

## Results

- `exists_integerNorm_sub_mem_of_le_apfRamificationBound`: every integer of `E` is congruent to a norm from `F` modulo the `r`-th power of the maximal ideal, for `r ≤ ⌈(p − 1)/p · b⌉`.
- `truncatedNorm_surjective`: the truncated norm is surjective.
- `addVal_integerNorm_of_totallyRamified`: under total ramification, `integerNorm` preserves the normalized additive valuation, also at `0`.
- `truncatedNorm_truncatedAddVal_mk`, `truncatedNorm_truncatedAddVal`: the truncated norm sends `truncatedAddVal` at precision `s` to its minimum with `r`.
- `truncatedNorm_comp`: for a tower `E ≤ F ≤ G` and precisions `r ≤ s ≤ t`, the truncated norms compose, provided each of the three steps satisfies its own hypotheses.
- `truncatedNorm_self`: for `E ≤ E`, the truncated norm is the reduction map `Ideal.Quotient.factor`.
- `exists_surjective_truncatedNorm_self`: for `E ≤ E` and any `r ≤ s`, the reduction map is a surjective ring homomorphism compatible with `integerNorm E E`; no bound is needed.

## Proofs

Additivity modulo the `r`-th power comes from `integerNorm_add_congruence_of_le_apfRamificationBound`, in the file on finite layers; multiplicativity and preservation of ideal powers come from the file on integral norms. Approximate surjectivity is `exists_intNorm_sub_mem_maximalIdeal_pow`, applied to the spectral integer rings.

## To watch for

- `truncatedNorm` takes as arguments the three hypotheses on `F/E`: total ramification `he` (ramification index equal to the degree), the degree `hd`, and the bound `hb`.
- `truncatedNorm_comp` assumes these for `E ≤ G` and `F ≤ G` separately; it does not derive those for `E ≤ G` from the two steps. `truncatedNorm_self` likewise takes them for `E ≤ E`.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Estimates/Truncated.lean` (SHA-256 of the source file `3f42987e2cb9dde3aa92d370900a6ee909e0b5d53d2f4dc0694119315ccfc522`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
