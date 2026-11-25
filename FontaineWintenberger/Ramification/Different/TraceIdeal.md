# Trace ideals and the different

Module `FontaineWintenberger.Ramification.Different.TraceIdeal`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

A fractional ideal has integral traces exactly when it lies in the inverse different. For discrete valuation rings this gives an exact formula for the trace of each power of the maximal ideal.

## General statements

Here `A` is an integrally closed domain with fraction field `K`, `L/K` is finite separable, and `B` is a Dedekind domain, the integral closure of `A` in `L`, with fraction field `L`.

- `trace_integral_iff_le_codifferent`: for a fractional ideal `I` of `B`, `Algebra.trace K L x` lies in `A` for all `x ∈ I` if and only if `I ≤ (differentIdeal A B)⁻¹`.
- `trace_principal_iff_le_mul_codifferent`: for `a ≠ 0` in `K`, `Tr(I) ⊆ aA` if and only if `I ≤ (a) · (differentIdeal A B)⁻¹`.
- `trace_principal_iff_mul_different_le`: the same condition is equivalent to `I · differentIdeal A B ≤ (a)`.
- `intTrace_mem_principal_iff_mul_different_le`: with `B` finite over `A`, for an ideal `I` of `B` and `a ≠ 0` in `A`, `Algebra.intTrace A B` maps `I` into `Ideal.span {a}` if and only if `I * differentIdeal A B` is contained in the extension of `Ideal.span {a}` to `B`.

## Discrete valuation rings

Now `A` and `B` are discrete valuation rings, `B` finite over `A` with a local, injective structure map.

- `intTraceIdeal A B I`: the ideal of `A` that is the image of the ideal `I` of `B` under `Algebra.intTrace A B`. `intTraceIdeal_le_iff` unfolds containment in an ideal `J` of `A`.
- `ideal_eq_pow_emultiplicity`: a nonzero ideal `I` of `B` equals the power of the maximal ideal with exponent `(emultiplicity (maximalIdeal B) I).toNat`.
- `intTraceIdeal_pow_le_pow_iff`: with fraction fields `K`, `L` as above (`L/K` finite separable, `B` the integral closure), `Tr(𝔪_B^n) ⊆ 𝔪_A^s` if and only if `e · s ≤ d + n`, where `e` is the ramification index and `d` the exponent of the different.
- `intTraceIdeal_pow`: `Tr(𝔪_B^n) = 𝔪_A^⌊(d + n)/e⌋`, for every natural number `n`.
- `extensionValuationSubring_intTraceIdeal_pow`: the same formula for `𝒪[K]` and the valuation ring of a valuation `w` on a finite separable extension `L` extending that of a complete discretely valued field `K`.

## Proofs

The first equivalence is Mathlib's description of the different as the inverse of the trace dual of `B`; the principal case follows by scaling with `a⁻¹`. The formula for `Tr(𝔪_B^n)` follows from the containment criterion.

## What to watch for

- `intTraceIdeal` is the library's definition, made only for discrete valuation rings.
- `d` is `(emultiplicity …).toNat`; `(d + n)/e` is division in `ℕ`.
- No hypothesis on residue fields; the extension need not be Galois. Only `n ≥ 0` is treated.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Different/TraceIdeal.lean` (SHA-256 of the source file `748a11957a7018d8be326ab794cecdd81feecf8a5e3202363127f7b502072bfc`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
