# APF invariants of a finite extension that need not be normal

Module `FontaineWintenberger.APF.Finite.Nonnormal`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field, `L/K` a finite Galois extension with group `G`, and `M` an intermediate field with fixing subgroup `H`, not assumed normal over `K`. The file computes the APF invariants of `M/K` inside `G`, with `G^u` the upper ramification groups on `spectralIntegerRing K L`.

## Results

For `E` a finite Galois intermediate field of `SeparableClosure K` and `M` an intermediate field of `E`:

- `apfSubgroup_map_eq_comap_sup_upper`: for `u ≥ -1`, the APF subgroup of the image of `M` is the preimage of `H ⊔ Gal(E/K)^u` under restriction from the absolute Galois group.
- `fixingSubgroup_sup_upper_inf_zero`: `(H ⊔ G^u) ⊓ G^0 = (H ⊓ G^0) ⊔ G^u` for `u ≥ 0`.
- `apfInertiaIndex_map_eq_subgroupRelIndex`, `apfIndex_eq_subgroupRelIndex`: for `u ≥ 0`, `apfIndex K M u` is the relative index of `(H ⊓ G^0) ⊔ G^u` in `G^0`.
- `apfPsi_eq_subgroup_herbrand_comp_inverse`: for `u ≥ -1`, `apfPsi K M u` is the Herbrand function of `H` applied to the inverse Herbrand function of `G` at `u`.
- `apfPhi_eq_herbrand_comp_subgroup_inverse`: `apfPhi K M v` is the Herbrand function of `G` applied to the inverse Herbrand function of `H` at `v`.

For an abstract finite Galois extension `L/K` and an intermediate field `M`, the same statements: `apfIndex_eq_subgroupRelIndex_of_finiteGalois`, `apfPsi_eq_subgroup_herbrand_comp_inverse_of_finiteGalois`, `apfPhi_eq_herbrand_comp_subgroup_inverse_of_finiteGalois`. Further:

- `apfSubgroup_fieldRange_index_eq_fixingSubgroup_sup_upper_index`: for an embedding `j` of `L` in the separable closure and `u ≥ -1`, the index of the APF subgroup of `j(M)` equals the index of `H ⊔ G^u` in `G`.
- `apfSubgroup_fieldRange_eq_top_iff_fixingSubgroup_sup_upper_eq_top`: that subgroup is everything if and only if `H ⊔ G^u = ⊤`.
- `apfRamificationBound_eq_sSup_fixingSubgroup_sup_upper`: `apfRamificationBound K M` is the supremum, in the extended reals, of the `u ≥ -1` with `H ⊔ G^u = ⊤`.

`fixingSubgroup_map_autCongr` is a lemma of field theory: an isomorphism of extensions carries the fixing subgroup of `M` to that of its image.

## Proofs

The preimage formula comes from the Galois case and surjectivity of restriction. The formulas for `apfPsi` rest on results of the ramification part of the library that express the composite of the Herbrand function of a subgroup with the inverse Herbrand function of the group as an integral of relative indices (`subgroup_herbrandFunction_comp_inverse_eq_integral`). The abstract case is transported along an embedding of `L`.

## What to watch for

- The Herbrand functions of `G` and of its subgroup `H` are the library's `herbrandFunction` and `inverseHerbrandFunction`, both taken on the integer ring of `L`.
- The statements hold for `u ≥ -1` (functions) or `u ≥ 0` (indices).

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Finite/Nonnormal.lean` (SHA-256 of the source file `14afa250de1300ca975f9b28336efbbba6897e59496e9d8b2e1c10defdf7b5f2`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
