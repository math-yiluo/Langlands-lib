# Uniformizers detected by the normalized valuation

Module `FontaineWintenberger.Mathlib.RingTheory.DiscreteValuationRing`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file contains one theorem, `IsDiscreteValuationRing.irreducible_of_valuation_eq_exp_neg_one`. Let `F` be a field and `A` a valuation subring of `F` that is a discrete valuation ring. If an element `z` of `A` has value `exp(−1)` for the valuation of `F` attached to the maximal ideal of `A` (`(maximalIdeal A).valuation F`, with values in `WithZero (Multiplicative ℤ)`), then `z` is irreducible in `A`, that is, a uniformizer.

## Proof

Write `z = u · ϖ^n` with `u` a unit and `ϖ` irreducible. The valuation of `z` is `exp(−n)`, so `n = 1` and `z` is an associate of `ϖ`.

## Points to watch

- The valuation is multiplicative: value `exp(−1)` corresponds to additive valuation `1`.
- The theorem is in Mathlib's namespace `IsDiscreteValuationRing`; the file's header names `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing` as the intended place for it in Mathlib.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/RingTheory/DiscreteValuationRing.lean` (SHA-256 of the source file `47deb4d5c07da7e0fe7f3ba38d5a49ecc633773e8a3c131e8a4fb28729e1857d`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
