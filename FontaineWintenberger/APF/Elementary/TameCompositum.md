# The tame compositum and the scaling of Herbrand functions

Module `FontaineWintenberger.APF.Elementary.TameCompositum`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field and `Ω/K` a finite Galois extension of normed fields with group `G`. Let `P` be the wild inertia group (the lower ramification group of index `1` on `spectralIntegerRing K Ω`), `A` its fixed field, and `e` the ramification index of `A/K`. For an intermediate field `F`, the file compares the ramification of `F/K` with that of the compositum `A ⊔ F` over `A`: parameters are multiplied by `e`.

## Results

Write `H` for the fixing subgroup of `F`.

- `exists_apfRamificationBound_wild_compositum`: for a subgroup `J ≠ ⊤` with `J ⊔ P = ⊤` and `F` its fixed field, there is a real `b ≥ 0` with `apfRamificationBound K F = b` and `apfRamificationBound A (A ⊔ F) = e · b`.
- `exists_apfRamificationBound_wild_compositum_of_totallyRamified`: the same when `F/K` is totally ramified of degree `p ^ n > 1`, `p` the residue characteristic.
- `wild_compositum_extendScalars_eq_fixedField`: for any `F`, the field `A ⊔ F` over `F` is the fixed field of the wild inertia group of `Gal(Ω/F)`.
- `wild_fixedField_apfPsi`: `apfPsi K A u = e · u` for `u ≥ 0`. `wild_compositum_apfPsi_over_right`: `ψ` of `A ⊔ F` over `F` is multiplication by its ramification index.
- `wild_compositum_ramificationIdx_eq`: if `H ⊔ P = ⊤`, the ramification index of `A ⊔ F` over `F` equals `e`.
- `wild_compositum_apfPsi_scaling`: if `H ⊔ P = ⊤` and `u ≥ 0`, then `apfPsi A (A ⊔ F) (e · u) = e · apfPsi K F u`. `wild_compositum_apfPhi_scaling` is the same for `φ = apfPhi`.
- `wild_compositum_herbrand_scaling_of_totallyRamified`: for `F/K` totally ramified of degree `p ^ n` (the trivial extension included), these statements hold.

## Proofs

The upper group over `A` at `e · u` matches that over `K` at `u`, by finite base change, and positive upper groups lie in `P`. The scaling of `ψ` writes `ψ` of `A ⊔ F` over `K` through `A` and through `F` by transitivity. That `H ⊔ P = ⊤` in the totally ramified `p`-power case is `fixedField_sup_wild_eq_top`.

## What to watch for

- The condition `J ⊔ P = ⊤` (or `H ⊔ P = ⊤`) is a hypothesis of the general statements; only the totally ramified `p`-power case derives it.
- `F` need not be normal over `K`.
- Total ramification is stated on the valuation ring of `F` cut out by the spectral valuation of `Ω`; the residue characteristic is given as `CharP` on the residue field of `spectralIntegerRing K Ω`.
- `A ⊔ F` over `A` or over `F` is `IntermediateField.extendScalars`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Elementary/TameCompositum.lean` (SHA-256 of the source file `6ce4b26bc74a2272bfdae4734b7d372731f06baefb03be31e1023662eb2a805f`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
