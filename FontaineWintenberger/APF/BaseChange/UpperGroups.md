# Upper ramification groups after a finite change of base

Module `FontaineWintenberger.APF.BaseChange.UpperGroups`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field and `M/K` a finite separable extension. The file proves that upper ramification groups over `M` are obtained from those over `K` by intersecting with the subgroup fixing `M` and changing the parameter by `ψ = apfPsi K M`: in short `G_M^v = G_M ∩ G_K^u` with `v = ψ(u)`, for `u ≥ -1`, first in a finite Galois extension, then in the separable closure. The base `M` is not assumed normal over `K`.

## Finite Galois level

- `finiteBase_upperRamificationGroup_of_finiteGalois`: for a finite Galois extension `E/K` of normed fields and an intermediate field `M`, the upper group of `Gal(E/M)` at `ψ(u)` is the image, under `M.fixingSubgroupEquiv`, of the upper group of `Gal(E/K)` at `u` intersected with the fixing subgroup of `M`. `finiteBase_upperRamificationGroup` is the same for `E` a finite Galois intermediate field of `SeparableClosure K` with the spectral norm.
- For an abstract complete normed field `M` over `K` with an algebra structure to such a layer `E`: `finiteTowerAutEquivImage` identifies `Gal(E/M)` with the Galois group of `E` over the image of `M`; `finiteTower_spectralIntegerRing_eq` and `finiteTowerSpectralIntegerRingEquiv` identify the two integer rings, compatibly with the actions; `finiteTower_upper_map_autEquivImage` transports upper groups.
- `finiteTower_range_restrictScalarsHom`: the image of restriction of scalars `Gal(E/M) → Gal(E/K)` is the fixing subgroup of the image of `M`.
- `finiteTower_upper_map_restrictScalars`, `finiteTower_mem_upper_iff_restrictScalars` (for `M` finite separable): `g ∈ Gal(E/M)^v`, `v = ψ(u)`, if and only if its restriction of scalars lies in `Gal(E/K)^u`.

## Separable closure

Here `M` is a finite intermediate field of `SeparableClosure K` with the spectral norm.

- `mem_upperRamificationGroupInfinite_base_iff`, `mem_upperRamificationGroupInfinite_containing_base_iff`: membership in the infinite upper groups over `M`, and over `K`, can be tested on the finite Galois layers over `K` that contain `M`.
- `mem_upperRamificationGroupInfinite_finiteBase_iff`: an `M`-automorphism of `SeparableClosure K` lies in the upper group over `M` at `ψ(u)` if and only if, as a `K`-automorphism, it lies in `G_K^u`.
- `absoluteGaloisBaseChange_mem_upper_iff`, `absoluteGaloisBaseChange_map_upper`: the same through the identification `absoluteGaloisBaseChangeEquiv K M` of `G_M` with the fixing subgroup of `M`; the image of `G_M^v`, `v = ψ(u)`, is the fixing subgroup of `M` intersected with `G_K^u`.

## Proofs

The finite statement rests on the expression of `apfPsi K M` through Herbrand functions of `Gal(E/K)` and its subgroup (`apfPsi_eq_subgroup_herbrand_comp_inverse_of_finiteGalois`) and on the base change of upper groups (`finiteBase_upper_map_fixingSubgroupEquiv`).

## What to watch for

- Upper groups are the library's `upperRamificationGroup`, attached to the action on the spectral integer ring `spectralIntegerRing`, and `upperRamificationGroupInfinite`.
- All statements assume `u ≥ -1`; the main ones assume a perfect residue field.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/BaseChange/UpperGroups.lean` (SHA-256 of the source file `d30cea18d246018815ed4eda46abd6e6e33d8401ad27dccbb34bc097565502bb`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
