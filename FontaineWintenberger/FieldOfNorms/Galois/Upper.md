# Finite upper ramification comparison for the field of norms

Module `FontaineWintenberger.FieldOfNorms.Galois.Upper`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field, `L/K` a separable APF extension, and `N/L` a finite Galois extension with `N/K` separable, APF and infinite. The file shows that an automorphism lying in the `u`-th upper ramification group over `K` and fixing `L` restricts on `N` to an element of the norm-field upper ramification group `FieldOfNorms.upperRamificationGroup K L N` at the parameter `apfPsi K L u`, the inverse Herbrand value of `L/K`. This is one inclusion of Wintenberger's Corollary 3.3.6, at a finite stage.

## Main results

* `upperRamificationGroup_restrictScalars_eq`: for finite extensions `K ⊆ C ⊆ E` with `E/K` separable and `u ≥ -1`, the upper ramification group of `E ≃ₐ[C] E` computed on `spectralIntegerRing K E` equals the one computed on `spectralIntegerRing C E`; the two rings are the same valuation subring.
* `exists_galois_stable_goodFiniteLayer_apfPsi_eq`: for a finite subextension `E` of `N/K` and a real `u`, there is a finite `D ⊇ E` in `N/K` that is a good finite layer (`IsGoodFiniteLayer K L D`), is stable under `N ≃ₐ[L] N`, contains a primitive element of `N/L`, whose pullback `D ∩ L` satisfies `apfPsi K (D ∩ L) u = apfPsi K L u`, and on which every `σ` in `N ≃ₐ[L] N` has ramification number equal to `FieldOfNorms.ramificationNumber K N σ`.
* `FieldOfNorms.restrictNormal_mem_upperRamificationGroup_tower`: let `M/K` be Galois containing `N`, `u ≥ -1`, and `σ` in `M ≃ₐ[L] M` whose restriction of scalars to `K` lies in `upperRamificationGroupInfinite K M u`. Then `σ.restrictNormal N` lies in `FieldOfNorms.upperRamificationGroup K L N (apfPsi K L u)`.
* `FieldOfNorms.restrictNormal_mem_upperRamificationGroup`: the same with `M = SeparableClosure K` and `absoluteUpperRamificationGroup K u`.

## Proofs

The existence statement combines `IsAPF.exists_finiteIntermediateField_apfPsi_eq` (a finite layer of `L/K` beyond which `apfPsi` at `u` is stable) with `exists_galois_stable_goodFiniteLayer_ramificationNumber_eq`. For the comparison, take such a `D` with pullback `C`. The hypothesis on `σ` passes to the finite base `C` with parameter `apfPsi K C u` (`mem_upperRamificationGroupInfinite_finiteBase_tower_iff`), then to the finite Galois extension `D/C` (`restrictNormal_mem_upperRamificationGroup_of_finite`), and is transported to `N ≃ₐ[L] N` through `galoisFiniteLayerEquiv` and `galoisFiniteLayerEquiv_map_upperRamificationGroup`.

## Remarks

* Only the inclusion "upper group over `K` restricts into the norm-field upper group" is proved here; the equality is in `FontaineWintenberger.FieldOfNorms.Galois.UpperLimit`.
* The comparison theorems need `u ≥ -1`.
* The tower theorems carry, as instance hypotheses, algebra structures of `L`, `M` (or `N`) over `SeparableClosure K` with their scalar-tower compatibilities.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, Corollary 3.3.6.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Galois/Upper.lean` (SHA-256 of the source file `20fd7da2d21d2486f3684be067b55dd7557d7bfd8c37f137ecb4ec6afdad54f3`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
