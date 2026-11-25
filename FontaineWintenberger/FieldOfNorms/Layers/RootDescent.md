# Disjoint root adjunction at a full upper stage

Module `FontaineWintenberger.FieldOfNorms.Layers.RootDescent`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field, `L` an intermediate field of `SeparableClosure K` over `K`, and `x` a root of a monic polynomial `f` over `𝒪[K]` whose image over `K` is separable. Fix a real `b` with `(deg f)! · v(disc f) ≤ b`, and assume the "full upper product" condition `apfSubgroup K L b = ⊤`: the subgroup fixing `L` and the upper ramification group `absoluteUpperRamificationGroup K b` together generate the whole Galois group. The file shows that `K(x)` is then linearly disjoint from `L` over `K`, so that `L ⊗_K K(x) ≅ L(x)`, and that the condition is inherited by `L(x)` over the new base `K(x)`.

## Main definitions

* `rootFieldToCompositum K L x`: the inclusion `K(x) → L(x)`.
* `rootAdjunctionTensorMap K L x`: the multiplication map `L ⊗_K K(x) → L(x)`.
* `rootAdjunctionTensorEquivOfFullUpper`, `rootAdjunctionTensorEquivCommonClosure`: this map as an isomorphism, under the hypotheses above.

## Main results

Under the hypotheses above:

* `exists_fixing_aut_root_of_fullUpper`: every conjugate of `x` over `K` is `h x` for an automorphism `h` fixing `L`.
* `minpoly_natDegree_eq_of_fullUpper`, `minpoly_map_eq_of_fullUpper`: the minimal polynomial of `x` over `L` is that over `K`.
* `linearDisjoint_root_of_fullUpper`, `finrank_root_adjunction_eq_of_fullUpper`: `K(x)` is linearly disjoint from `L`, and `[L(x):L] = [K(x):K]`.
* `rootAdjunctionTensorMap_bijective_of_fullUpper`: the multiplication map is bijective.
* `absoluteUpper_le_root_fixingSubgroup` (no hypothesis on `L`): the upper group at `b` fixes `K(x)`. `apfSubgroup_root_compositum_eq_fixingSubgroup`: `apfSubgroup K L(x) b` is the subgroup fixing `K(x)`.

With perfect residue field, `D = K(x)` and `M = L(x)`:

* `isAPF_rootAdjunction`, `rootAdjunction_not_finite`: `M/K` is APF, respectively infinite, if `L/K` is.
* `rootAdjunction_fullUpper`: the image of `M` in `SeparableClosure D` has full upper product over `D` at the parameter `apfPsi K D b`.
* `apfPsi_le_rootAdjunction_firstBound`, `le_rootAdjunction_firstBound`: `apfPsi K D b ≤ apfRamificationBound D M`, hence `b ≤ apfRamificationBound D M`.

The results from linear disjointness onward have `..._commonClosure` variants for an arbitrary separable closure `Ω` of `K` (`IsSepClosure K Ω`), where the hypothesis reads `L.fixingSubgroup ⊔ upperRamificationGroupInfinite K Ω b = ⊤`.

## Proofs

The input is `absoluteUpperRamificationGroup_fixes_integral_polynomial_root`: the upper group at `b` fixes the roots of `f`. Since that group is normal, any automorphism is `h · u` with `h` fixing `L` and `u` in it, so the conjugates of `x` over `K` stay conjugate over `L`; counting roots gives the degree equality, and `linearDisjoint_adjoin_of_minpoly_lifts` gives disjointness.

## Remarks

* The full upper product condition is a hypothesis (`htop`) of each theorem; the file does not produce it.
* Neither `L` nor `K(x)` is assumed normal over `K`.
* The statements over `D` use spectral-norm structures on `D` declared as local instances.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Layers/RootDescent.lean` (SHA-256 of the source file `8248047acb47c523fb85dc663a9ada6acae9051f2b3af41682af98378e559d11`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
- The file did not compile on the Library's Mathlib, which is older than the one the source was written for, and was repaired: Unpacked the root-field element in both pure-tensor proofs and the scalar-tower proof, and used the tower identity for the common-closure embedding to resolve four kernel timeouts.
