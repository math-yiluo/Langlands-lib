# Invariance of the residue degree

Module `FontaineWintenberger.Ramification.Upper.ResidueEquiv`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field. For a separable algebraic extension `L` of `K`, the residue degree here is the dimension of the residue field of `spectralIntegerRing K L` over the residue field of `𝒪[K]`.

- `spectral_residueDegree_algEquiv`: if `e : L ≃ₐ[K] M` is an isomorphism between two separable extensions of `K`, then `L` and `M` have the same residue degree.
- `extensionValuationSubring_residueDegree_eq_spectral`: if `L/K` is finite separable and `w` is any valuation on `L` extending that of `K`, the residue field of the valuation ring of `w` has the same dimension over the residue field of `𝒪[K]` as that of the spectral integer ring.

Both come from an isomorphism of the integer rings over `𝒪[K]`, to which Mathlib's `IsLocalRing.ResidueField.mapAlgEquiv'` is applied: in the first case `spectralIntegerRingEquiv K e`, in the second the isomorphism between two integral closures of `𝒪[K]` in `L`.

Degrees are `Module.finrank`, which is zero for an infinite-dimensional extension; the first statement does not assume `L/K` finite.

Reference: Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Upper/ResidueEquiv.lean` (SHA-256 of the source file `d6b25ad9be073a6d2fdcd56fea2a4c684d947134dbc0eb382fc2c0a7359fa664`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
