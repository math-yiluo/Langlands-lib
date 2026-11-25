# Ramification on finite Galois extensions of the field of norms

Module `FontaineWintenberger.FieldOfNorms.Galois.Ramification`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy the library's class `IsPerfectResidueLocalField`, and let `L ⊆ N` be infinite separable APF extensions of `K` with `N/L` finite Galois. The Galois group of `N/L` acts on the valuation ring of `FieldOfNorms K N`. The file shows that this group, with its ramification orders and its upper ramification filtration, can be read on one finite intermediate field `D` of `N/K`: a layer that is stable under the group, "good" in the sense of `IsGoodFiniteLayer`, and above any prescribed finite field.

## Definitions

- `FieldOfNorms.integerAutHom`: `FieldOfNorms.integerAut` as a group homomorphism from `L ≃ₐ[K] L`.
- `FieldOfNorms.integerGaloisAction`: the resulting action of `N ≃ₐ[L] N` on the valuation ring of `FieldOfNorms K N`.
- `FieldOfNorms.upperRamificationGroup K L N u`: the library's `upperRamificationGroup` of `N ≃ₐ[L] N` for this action.
- `galoisFiniteLayerIntegerAction`: for a stable layer `D`, the action of `N ≃ₐ[L] N` on `spectralIntegerRing K D`.
- `galoisFiniteLayerEquiv`: for a stable `D` containing an element `α` with `L(α) = N`, the group isomorphism from `N ≃ₐ[L] N` to the Galois group of `D` over `D ∩ L` (`FiniteIntermediateField.pullback K L D`), given by restriction.

## Results

- `exists_finiteIntermediateField_forall_ramificationNumber_eq`: for a finite family of automorphisms of `L/K`, one finite intermediate field `E` works for all: above `E`, each finite-layer ramification number equals the one on the field of norms.
- `exists_galois_stable_goodFiniteLayer_ramificationNumber_eq`: above any finite `E` there is a good, stable `D` containing a primitive element of `N/L`, such that on every finite `F ⊇ D` the ramification number of each `σ` in `N ≃ₐ[L] N` equals its number on the field of norms.
- `galoisFiniteLayer_ramificationOrder_eq`, `galoisFiniteLayer_upperRamificationGroup_eq`: if the numbers agree at a stable `D`, the ramification orders agree, and so do the upper ramification groups for `u ≥ −1`.
- `isGalois_galoisStableFiniteLayer`, `galoisFiniteLayerRestrict_bijective`: a stable `D` is Galois over `D ∩ L`, and restriction is bijective when `D` contains a primitive element.
- `galoisFiniteLayerEquiv_map_upperRamificationGroup`: under the same hypothesis, `galoisFiniteLayerEquiv` maps `FieldOfNorms.upperRamificationGroup K L N u` onto the upper ramification group of the Galois group of `D` over `D ∩ L`, for `u ≥ −1`.
- `exists_galois_stable_goodFiniteLayer_upperRamificationGroup_eq`: above any finite `E` such a `D` exists.

## Proofs

The first result applies the transfer theorem `exists_finiteIntermediateField_ramificationNumber_eq` to each automorphism and takes an upper bound. Equality of filtrations follows from equality of orders (`upperRamificationGroup_eq_of_order_eq`) and transport along a group isomorphism (`upperRamificationGroup_map_mulEquiv`).

## To watch for

- `galoisFiniteLayer_ramificationOrder_eq` and the two theorems after it take the agreement of ramification numbers at `D` as a hypothesis `h`; only the existence theorems supply it.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, Proposition 3.3.2 and the proof of Corollary 3.3.6.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Galois/Ramification.lean` (SHA-256 of the source file `fa0ef2dc9d82b7e527dd3977eb33840c47283ec8fcfcaf44aa8449cd74087750`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
