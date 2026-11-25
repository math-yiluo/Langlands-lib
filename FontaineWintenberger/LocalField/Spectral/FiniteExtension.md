# The integer ring of a finite separable extension is a discrete valuation ring

Module `FontaineWintenberger.LocalField.Spectral.FiniteExtension`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy `IsCompleteDiscreteValuedField K` and let `L/K` be a finite separable field extension. The file studies `spectralIntegerRing K L`, the unit ball of the spectral norm on `L`, which is the integral closure of `𝒪[K]` in `L`.

## Main results

- Instances `spectralIntegerRing_moduleFinite`, `spectralIntegerRing_moduleFree`: it is a finite free module over `𝒪[K]`.
- `spectralIntegerRing_finrank`: its rank over `𝒪[K]` is `[L : K]`.
- Instance `spectralIntegerRing_isNoetherianRing`: it is noetherian.
- `spectralIntegerRing_not_isField`: it is not a field.
- Instance `spectralIntegerRing_isDiscreteValuationRing`: it is a discrete valuation ring.

## Proofs

Finiteness, freeness and the rank come from Mathlib's results on integral closures in finite separable extensions. A uniformizer of `𝒪[K]` is a nonzero non-unit, so the ring is not a field; a noetherian valuation ring that is not a field is a discrete valuation ring (`IsDiscreteValuationRing.TFAE`).

## Points to watch

- Separability of `L/K` is assumed; nothing is assumed on the residue field.

## References

Serre, *Local Fields*, Chapters I–II.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/LocalField/Spectral/FiniteExtension.lean` (SHA-256 of the source file `2800686f02d13d7c016cc0f04845a1ec758ff7443d38a6978c63f2fab201c5db`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
