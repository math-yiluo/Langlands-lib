# The ramification index and normalized valuations

Module `FontaineWintenberger.Ramification.Lower.Index`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `R → S` be an injective local homomorphism of discrete valuation rings, with maximal ideals `𝔪_R`, `𝔪_S`. The file identifies Mathlib's ramification index `e = (𝔪_S).ramificationIdx R` with the exponent of `𝔪_R S` and derives how the normalized valuation `addVal` scales.

- `exists_uniformizer_factor_ramificationIdx`: for a uniformizer `ϖ` of `R` there are a uniformizer `π` of `S` and a unit `u` with `ϖ = u · π^e` in `S`.
- `map_maximalIdeal_eq_pow_ramificationIdx`: `𝔪_R S = 𝔪_S^e`.
- `local_ramificationIdx_pos`: `e > 0`.
- `ramificationIdx_eq_addVal_uniformizer`: `e = addVal S ϖ` for a uniformizer `ϖ` of `R`.
- `addVal_algebraMap`: `addVal S x = e · addVal R x` for all `x ∈ R`, including `x = 0`.

A private lemma shows that any `e'` with `𝔪_R S = 𝔪_S^(e')` equals Mathlib's index.

## What to watch for

`S` is not assumed finite over `R`; injectivity is given as `FaithfulSMul R S`.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/Index.lean` (SHA-256 of the source file `596e5d892e738a05b994d13f2626f54585ab2e2d565d914aa8082dfd14e26473`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
