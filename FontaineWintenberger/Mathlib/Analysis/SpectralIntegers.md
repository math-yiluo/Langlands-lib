# Integral elements and the spectral valuation

Module `FontaineWintenberger.Mathlib.Analysis.SpectralIntegers`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be an ultrametric normed field with unit ball `OK`, and `L/K` an algebraic field extension. The file relates the spectral norm on `L` to integrality over `OK` and, for `K` complete, turns it into a valuation.

## Main definitions and results

- `isIntegral_iff_spectralNorm_le_one`: `x ∈ L` is integral over `OK` iff `spectralNorm K L x ≤ 1` (no completeness needed).

For `K` nontrivially normed and complete:

- `spectralValuation K L : Valuation L ℝ≥0`: the valuation `x ↦ spectralNorm K L x`; it extends the norm valuation of `K` (`spectralValuation_algebraMap`, instance `spectralValuation_hasExtension`).
- `spectralIntegerRing K L`: its valuation subring, the elements of spectral norm `≤ 1`.
- `spectralIntegerRing_eq_integralClosure`, instance `spectralIntegerRing_isIntegralClosure`: it is the integral closure of `OK` in `L`.
- `smul_spectralIntegerRing`, `spectralIntegerRing_decompositionSubgroup`: every `K`-automorphism of `L` preserves it.

## Proofs

Multiplicativity of the spectral norm is Mathlib's `spectralAlgNorm_mul`, which uses completeness.

## Points to watch

- Values lie in `ℝ≥0`; no discreteness or residue-field hypothesis is used.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/Analysis/SpectralIntegers.lean` (SHA-256 of the source file `45c09bc6f95e8eb3f65b087143ad87860b3d4523d08455a9ea21962f840ba5ca`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
