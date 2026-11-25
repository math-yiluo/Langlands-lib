# Estimates for the norm between finite layers

Module `FontaineWintenberger.FieldOfNorms.Estimates.FiniteLayer`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy `IsPerfectResidueLocalField K`, with residue characteristic `p`, and let `E ≤ F` be finite intermediate fields of a separable extension `L/K`. The norm `N` from `F` to `E` restricts to a multiplicative map `integerNorm E F hEF` between the spectral integer rings. The file gives congruences for this map when `F/E` is totally ramified of `p`-power degree: how far it is from being additive, and how it treats congruent elements. The bounds are expressed with the Herbrand function `apfPhi` and the ramification bound `apfRamificationBound` of `F/E`, where `E` carries the spectral norm.

## Results

All in the namespace `FiniteIntermediateField`. The first, second and fourth assume that the ramification index of `F/E` equals `[F : E]` and that `[F : E] = p ^ n`. Write `𝔪_E`, `𝔪_F` for the maximal ideals of the spectral integer rings.

- `integerNorm_sub_congruence_of_totallyRamified`: if `x − y ∈ 𝔪_F ^ r`, then `N(x) − N(y) ∈ 𝔪_E ^ ⌈apfPhi E F r⌉`. The trivial step `E = F` is included.
- `exists_integerNorm_add_congruence_of_totallyRamified`: if moreover `[F : E] > 1`, there is a real `b ≥ 0` with `apfRamificationBound E F = b` and `N(x + y) − N(x) − N(y) ∈ 𝔪_E ^ ⌈(p − 1)/p · b⌉` for all integers `x, y` of `F`.
- `integerNorm_add_sub_eq_zero_of_finrank_eq_one`: if `[F : E] = 1`, then `N(x + y) − N(x) − N(y) = 0`.
- `integerNorm_add_congruence_of_le_apfRamificationBound`: for any real `b` with `b ≤ apfRamificationBound E F`, `N(x + y) − N(x) − N(y) ∈ 𝔪_E ^ ⌈(p − 1)/p · b⌉`. This covers the trivial step, whose bound is `⊤`.

## Proofs

The corresponding estimates for a finite extension of a complete discretely valued field with its own normed structure are proved in an earlier file (`intNorm_sub_congruence_of_totallyRamified`, `exists_intNorm_add_congruence_of_totallyRamified`, for `Algebra.intNorm`). Here they are transported to the finite layers. The spectral integer rings of `E` and `F` over `K` are identified with `𝒪[E]` and with the spectral integer ring of `F` over `E`; these identifications are the identity on field elements, commute with the algebra maps and with the norms, and preserve ramification indices and powers of maximal ideals.
## Points to watch

- Total ramification and `p`-power degree are hypotheses of the theorems, stated as equalities; the file does not derive them. They hold on the wild tail of an APF extension, by another file.
- The ramification bound takes values in `EReal`; the last theorem is stated with a real lower bound so that the infinite case needs no separate statement.
## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §§2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Estimates/FiniteLayer.lean` (SHA-256 of the source file `ab4104810242bf5a9ce67e406745a7046daccabb7c161c92e308c4e577918afe`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
