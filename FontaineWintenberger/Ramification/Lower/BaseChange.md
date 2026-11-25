# Spectral integers after changing a finite base

Module `FontaineWintenberger.Ramification.Lower.BaseChange`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete nonarchimedean normed field and `E` an algebraic extension carrying a compatible ultrametric norm. The library's ring of integers `spectralIntegerRing K E` is defined from the spectral norm over `K`; the file shows it does not change when `K` is replaced by a finite intermediate field `M`.

- `spectralIntegerRing_eq_normedUnitBall`: for a normed field `L` that is an algebraic normed `K`-algebra with ultrametric distance, `spectralIntegerRing K L = 𝒪[L]`, the unit ball of the norm of `L`.
- `finiteBase_spectralIntegerRing_eq`: `spectralIntegerRing K E = spectralIntegerRing M E` as valuation subrings of `E`, for `M` an intermediate field finite over `K`.
- `finiteBaseSpectralIntegerRingEquiv K E M`: the resulting ring isomorphism, the identity on elements.
- `finiteBaseSpectralIntegerRingEquiv_smul`: it intertwines the action of `M.fixingSubgroup` with that of `E ≃ₐ[M] E` under `M.fixingSubgroupEquiv`.

The first statement holds because the norm of `L` equals the spectral norm.

## What to watch for

`K` need not be discretely valued here; completeness of `M` is a local instance.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/BaseChange.lean` (SHA-256 of the source file `9872ade5b3a7c703660664b7b377c5913bcf80fc51dbc402aeec40c30be38942`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
