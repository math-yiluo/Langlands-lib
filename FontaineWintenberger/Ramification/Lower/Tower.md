# Normalized valuations and ramification indices in towers

Module `FontaineWintenberger.Ramification.Lower.Tower`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a local injective map `R → S` of discrete valuation rings with fraction fields `K ⊆ L`, the file compares the normalized valuations of `K` and `L` (Mathlib's adic valuations at the maximal ideals) and records multiplicativity of ramification indices.

- `normalizedValuation_algebraMap`: for `x` in `K`, the valuation of `x` in `L` is its valuation in `K` raised to the ramification index `e` of `S` over `R`.
- `normalizedValuation_hasExtension` (instance): the valuation of `L` extends that of `K`.
- `local_ramificationIdx_tower`: in a tower `R → S → T` with `S → T` a local injective map of discrete valuation rings, ramification indices multiply.
- `extensionValuationSubring_map_maximalIdeal`, `extensionValuationSubring_normalizedValuation_algebraMap`: for a complete discretely valued field `K`, a finite separable `L/K` and a valuation `w` on `L` extending that of `K`, the maximal ideal of `𝒪[K]` generates the `e`-th power of the maximal ideal of the valuation ring of `w`, and the first result holds for these rings.

Valuations are multiplicative, so scaling appears as a power.

Reference: Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/Tower.lean` (SHA-256 of the source file `0b3857703366cd0d1a0ff14985d15d0d5c4b9cc38d47fab907339a1c04aeca67`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
