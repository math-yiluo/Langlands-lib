# Positivity, triangularity and weight permutation

Author: Worker 1398.

* `ℓ_root_pos_or_neg`, `isPos_iff_ℓ_pos`: a root is positive for the base `b` (Mathlib
  `Base.IsPos`, via `exists_root_eq_sum_int` and `height_eq_sum`) exactly when the dominant
  functional `ℓ` is positive on it; `ℓ` never vanishes on a root.
* `IsUT`: nonzero entries `(c, d)` are diagonal entries equal to `1` or have
  `ℓ(wt d) < ℓ(wt c)`. Such matrices are block triangular (`blockTriangular_of_isUT`), closed
  under products, and under inverses (via Mathlib `blockTriangular_inv_of_blockTriangular` and
  the `(c, d)` entry of `g⁻¹ g = 1`); `utSub` is the resulting subgroup, and it contains `U⁺`
  (`isUT_x`, `posSub_le_utSub`).
* `IsWeightPerm`: nonzero entries `(c, d)` have `wt c = w (wt d)`; every element of `N` has this
  form (closure induction, using `weyl_weight` and `n_i⁻¹ = n_i (n_i²)⁻¹`).
* `eq_one_of_isUT_of_isWeightPerm` and `borelSub_inf_weylSub : B ⊓ N = T` (Steinberg,
  *Lectures on Chevalley groups*, Theorem 4(a,b), pp.35–36): an element `t u` of `B ∩ N` has `u` both
  unitriangular and weight-permuting, hence `u = 1`.
