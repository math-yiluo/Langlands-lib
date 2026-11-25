# Uniform continuity of valuation-preserving ring isomorphisms

Module `FontaineWintenberger.Mathlib.Analysis.UniformContinuity`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file contains one theorem, `valuedRingEquiv_uniformContinuous`. Let `R` and `S` be fields with `Valued` structures taking values in the same linearly ordered commutative group with zero `Γ₀`, and let `e : R ≃+* S` be a ring isomorphism with `v(e x) = v(x)` for all `x`. Then `e` is uniformly continuous for the valuation uniformities.

## Proof

It suffices to prove continuity at `0` of the additive map. A basic neighbourhood of `0` in `S` is given by a unit `γ` of the value group of `S`; writing `γ` as the value of a quotient `r/s` in `S`, the neighbourhood of `0` in `R` defined by the value of `e⁻¹(r/s)` is sent into it.

## Points to watch

- Neither valuation is assumed surjective onto `Γ₀`: the neighbourhood bases are indexed by the actual value groups (`Valued.hasBasis_nhds_zero`).
- Only one direction is stated; for the inverse, apply the theorem to `e.symm`.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/Analysis/UniformContinuity.lean` (SHA-256 of the source file `64f5216a1aca74d03e6ddb54aeeea8f0fe8d0e0c87bd3427272fbfa7500cbe87`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
