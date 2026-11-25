# The action of the full automorphism group on the spectral integers

Module `FontaineWintenberger.Ramification.Lower.GaloisGroup`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete nonarchimedean normed field and `L/K` algebraic, with `OL = spectralIntegerRing K L`. The decomposition subgroup of `OL` is all of `L ≃ₐ[K] L` (proved elsewhere); this file transports the action and the ramification notions to the full group.

- `spectralDecompositionEquiv K L`: the group isomorphism from the decomposition subgroup onto `L ≃ₐ[K] L`, given by inclusion.
- `spectralIntegerRingGaloisAction` (an instance): the action of `L ≃ₐ[K] L` on `OL` by ring automorphisms, with `(g • x : L) = g x`. By further instances it is faithful and commutes with `𝒪[K]`.
- `spectralIntegerRing_galois_mem_lower_iff`, `spectralIntegerRing_galois_order`: the lower ramification groups and `ramificationOrder` for the full group agree with those of the decomposition subgroup (`ValuationSubring.lowerRamificationGroupInt`, `ValuationSubring.ramificationOrder`).
- `spectralIntegerRing_galois_normalizedValuation`: every automorphism preserves the adic valuation of the maximal ideal of `OL` on `L`.

## What to watch for

`K` need not be discretely valued, nor `L/K` finite; the statements on order and valuation assume `OL` is a discrete valuation ring.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/GaloisGroup.lean` (SHA-256 of the source file `215d0e1afc394f2ae6a163f3b5f4d9274e5774b8caa400118d12f8832df21a81`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
- The statement of `spectralIntegerRing_galois_mem_lower_iff` names the lower group of the decomposition subgroup `ValuationSubring.lowerRamificationGroupInt`, which the source calls `ValuationSubring.lowerRamificationGroup` (renamed in `FontaineWintenberger.Ramification.Lower.Basic` because the Library declares the same full name).
