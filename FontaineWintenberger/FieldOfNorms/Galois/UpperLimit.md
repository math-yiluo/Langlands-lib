# Upper ramification in the relative field of norms

Module `FontaineWintenberger.FieldOfNorms.Galois.UpperLimit`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field and `L/K` an infinite separable APF extension. The file defines an upper ramification filtration attached to the relative field of norms, as a filtration of the Galois group of an extension of `L`, and proves Wintenberger's Corollary 3.3.6: it is the upper filtration over `K`, restricted to the automorphisms fixing `L`, after the change of parameter `apfPsi K L`.

## Definition

* `RelFieldOfNorms.upperRamificationGroup K L Ω u`, for `Ω/K` separable containing `L`: the subgroup of `Ω ≃ₐ[L] Ω` of those `σ` whose restriction to every finite Galois extension `N/L` inside `Ω` lies in `FieldOfNorms.upperRamificationGroup K L N u`. It is the intersection of the preimages under `AlgEquiv.restrictNormalHom N`; `RelFieldOfNorms.mem_upperRamificationGroup` unfolds membership.

## Main results

Let `M/K` be Galois containing `L`, and `u ≥ -1`.

* `RelFieldOfNorms.restrictScalars_mem_upperRamificationGroupInfinite_tower`: if `σ` in `M ≃ₐ[L] M` lies in `RelFieldOfNorms.upperRamificationGroup K L M (apfPsi K L u)`, then `σ`, viewed over `K`, lies in `upperRamificationGroupInfinite K M u`.
* `RelFieldOfNorms.upperRamificationGroup_eq_comap` (Corollary 3.3.6): `RelFieldOfNorms.upperRamificationGroup K L M (apfPsi K L u)` equals the preimage of `upperRamificationGroupInfinite K M u` under restriction of scalars `Gal(M/L) → Gal(M/K)`.
* `RelFieldOfNorms.map_upperRamificationGroup`: the image of that group in `Gal(M/K)` is `G^u ∩ H`, with `G = Gal(M/K)` and `H` the range of `Gal(M/L)`.

## Proofs

For the first result, a finite Galois `E/K` in `M` is placed inside a finite Galois `N/L` (a private lemma: adjoin a primitive element of `E` to `L` and take the normal closure). `exists_galois_stable_goodFiniteLayer_apfPsi_eq` gives a Galois-stable good finite layer `D ⊇ E` of `N/K` with pullback `C` and `apfPsi K C u = apfPsi K L u`. The restriction of `σ` to `N` corresponds under `galoisFiniteLayerEquiv` to an element of the upper group of `D/C`; it lifts to some `τ` in the upper group of `M/C` (`exists_lift_upperRamificationGroup_of_finite`), which lies in the `u`-th upper group over `K` and agrees with `σ` on `E`. The converse inclusion is `FieldOfNorms.restrictNormal_mem_upperRamificationGroup_tower` from `FontaineWintenberger.FieldOfNorms.Galois.Upper`. In the main theorem an embedding of `M` into `SeparableClosure K` is chosen to supply the algebra structures those lemmas require.

## Remarks

* The filtration is the library's own formulation: a subgroup of the Galois group `Gal(Ω/L)` of the original fields, tested on all finite Galois stages through the norm-field groups, and not defined as a ramification filtration of a Galois group of the field `RelFieldOfNorms K L Ω`.
* The comparison is stated for `u ≥ -1`, and for any Galois `M/K` containing `L`, not only a separable closure.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, Corollary 3.3.6.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Galois/UpperLimit.lean` (SHA-256 of the source file `2dc121ce0663a587ffd432752efe3cbabac6ce21d466cf19d55ec6a2d00040fb`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
