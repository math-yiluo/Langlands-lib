# The field fixed by wild inertia

Module `FontaineWintenberger.Ramification.Fields.Tame`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field (in the library's sense) with perfect residue field, `L/K` finite Galois with group `G`, `B = spectralIntegerRing K L`, `D` and `P` the zeroth and first lower ramification groups, and `F₁` the fixed field of `P` (called the tame field in the file's comments). The file shows that `F₁/K` has trivial upper ramification groups in positive degree and ramification index prime to the residue characteristic.

## Group-theoretic lemmas

For a finite group `G` acting on a discrete valuation ring `B`:

- `upperRamificationGroup_le_lower_one`: for `u > 0`, `upperRamificationGroup G u` is contained in the first lower ramification group.
- `lowerRamificationGroup_subgroup_zero_eq_top`: if a subgroup `H` lies in the zeroth lower group of `G`, then the zeroth lower group of `H` (acting by restriction) is all of `H`.
- `inverseHerbrandFunction_eq_card_inertia_mul`: if the action is faithful and the upper groups are trivial for all `u > 0`, then `inverseHerbrandFunction G u = |G₀| · u` for `u ≥ 0`. It follows from the integral formula for the inverse Herbrand function proved earlier.

## Results on the wild fixed field

- `wild_fixedField_top_ramificationIdx_eq_finrank`: the ramification index of `B` over the integers of `F₁` (valuation ring of the restricted spectral valuation) equals `[L : F₁]`.
- `wild_fixedField_upper_eq_bot`: for `u > 0`, the upper ramification group of `Gal(F₁/K)` at `u` is trivial.
- `wild_fixedField_ramificationIdx_eq_relIndex`: the ramification index of `F₁/K` equals `P.relIndex D`, that is `[D : P]`.
- `wild_fixedField_inverseHerbrandFunction`: for `u ≥ 0`, the inverse Herbrand function of `F₁/K` at `u` is `e(F₁/K) · u`.
- `wild_fixedField_ramificationIdx_coprime`: if `p` is the characteristic of the residue field of `B`, then `p` is coprime to `e(F₁/K)`.
- `wild_fixedField_isPGroup`: under the same hypothesis on `p`, `Gal(L/F₁)` is a `p`-group. This one does not need the residue field of `K` to be perfect.

## Proofs

The statement on upper groups uses compatibility of upper ramification groups with quotients (`restrictNormalHom_map_upperRamificationGroup_tower`): the image of `G^u` in `Gal(F₁/K)` is the upper group there, and `G^u ≤ P` is the kernel of restriction. Coprimality comes from `coprime_card_tameInertiaQuotient`, and the `p`-group property from `lowerRamificationGroup_one_isPGroup`, both from earlier files.

## What to watch for

- In the first result the integers of `F₁` are the valuation ring of the restricted spectral valuation; in the others they are `spectralIntegerRing K F₁`.
- The prime `p` enters through `CharP` of the residue field of `B`, so the statements with `p` concern positive residue characteristic.
- The ramification index of `F₁/K` is prime to `p`, but nothing is said about its residue degree.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Fields/Tame.lean` (SHA-256 of the source file `ab028354e5b3bb5ec055c6c6029228c3083b9f813dd8bf6e8f58d55609e77f90`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
