# APF invariants of a finite Galois extension

Module `FontaineWintenberger.APF.Finite.Galois`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field and `L/K` a finite Galois extension with group `G`. The file identifies the invariants defined through the absolute Galois group of `K` (the index `apfIndex`, the functions `apfPsi` and `apfPhi`, the bound `apfRamificationBound`) with the classical ones of `G`: upper ramification groups `G^u` on `spectralIntegerRing K L` and the Herbrand function of `G`.

## Results

For a finite Galois intermediate field `E` of `SeparableClosure K`:

- `apfSubgroup_eq_comap_upper`: for `u ≥ -1`, `apfSubgroup K E u` is the preimage of `Gal(E/K)^u` under restriction `G_K → Gal(E/K)`.
- `apfInertiaIndex_eq_upperRelIndex`: for `u ≥ 0`, `apfInertiaIndex K E u` is the relative index of `Gal(E/K)^u` in `Gal(E/K)^0`.
- `apfSubgroup_eq_top_iff_finite_upper_eq_top`: for `u ≥ -1`, `apfSubgroup K E u = ⊤` if and only if `Gal(E/K)^u` is the whole group.

For an abstract finite Galois extension `L/K`:

- `apfIndex_eq_upperRelIndex`: for `u ≥ 0`, `apfIndex K L u` is the index of `G^u` in `G^0`.
- `apfPsi_eq_inverseHerbrandFunction`: for `u ≥ -1`, `apfPsi K L u = inverseHerbrandFunction G u`.
- `apfPhi_eq_herbrandFunction`: for `u ≥ -1`, `apfPhi K L u = herbrandFunction G u`.
- `apfSubgroup_fieldRange_eq_top_iff_finite_upper_eq_top`: for any embedding `i` of `L` in the separable closure and `u ≥ -1`, `apfSubgroup K i.fieldRange u = ⊤` if and only if `G^u = ⊤`.
- `apfRamificationBound_eq_sSup_finite_upper`: `apfRamificationBound K L` is the supremum, in the extended reals, of the `u ≥ -1` with `G^u = ⊤`.

## Proofs

The absolute upper group maps onto the finite upper group under restriction (`absolute_map_upperRamificationGroup`, from the ramification part of the library), and the kernel of restriction is the fixing subgroup of `E`; hence the preimage formula. Indices then agree, and `apfPsi` is the integral of the same integrand as the inverse Herbrand function (`inverseHerbrandFunction_eq_integral_relIndex`). The abstract extension is transported to its image by `upperRamificationGroup_map_autCongr`.

## What to watch for

- `herbrandFunction` and `inverseHerbrandFunction` are the library's functions attached to the action of `G` on `spectralIntegerRing K L`; the identifications are stated for `u ≥ -1`.
- `apfPhi_eq_herbrandFunction` takes `IsAPF K L` as an instance argument, although finite extensions are APF.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Finite/Galois.lean` (SHA-256 of the source file `959906f4dc8ec46ae939d29276e3c6fa9c4946fd4b9eb99cadeece01fd403aa4`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
