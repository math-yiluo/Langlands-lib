# Adic completeness and Henselianity of the unit ball

Module `FontaineWintenberger.LocalField.Spectral.Henselian`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be an ultrametric normed field whose unit ball `𝒪[K]` is a discrete valuation ring with maximal ideal `𝔪`. The file identifies the norm topology on `𝒪[K]` with the `𝔪`-adic topology and deduces that `𝒪[K]` is Henselian when `K` is complete.

## Main results

- `mem_maximalIdeal_pow_iff_norm`: for an irreducible `π`, `x ∈ 𝔪^n ↔ ‖x‖ ≤ ‖π‖^n`.
- `unitBall_isAdic`: the topology of `𝒪[K]` is the `𝔪`-adic topology.
- `unitBall_completeSpace`: if `K` is complete, so is `𝒪[K]`.
- Instances `unitBall_isAdicComplete`, `unitBall_henselianLocalRing`: if `K` is complete, `𝒪[K]` is `𝔪`-adically complete and a Henselian local ring.
- Instance `spectralIntegerRing_henselianLocalRing`: for `K` with `IsCompleteDiscreteValuedField K` and `L/K` finite separable, `spectralIntegerRing K L` is a Henselian local ring.

## Proofs

Powers of `𝔪` are closed balls, which are open and form a basis at `0`. Henselianity follows from Mathlib's result for adically complete rings; for the extension, `L` is given its spectral norm.

## Points to watch

- The residue field is arbitrary.

## References

Serre, *Local Fields*, Chapters I–II.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/LocalField/Spectral/Henselian.lean` (SHA-256 of the source file `a53d46802bb2249f12525a545dfbfdec8808f2ca125ba4d2711031fab2a3d5f6`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
