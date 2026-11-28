import Langlands.Covering.KazhdanPatterson.Torus
import Langlands.GroupTheory.CentralCocycle
import Mathlib.GroupTheory.Commutator.Basic

/-! # The cocycle extension of the diagonal torus -/

namespace Langlands.KazhdanPatterson

open scoped BigOperators commutatorElement
open NormalizedTwoCocycle.Extension (inl sectionMap)

attribute [local instance] trivialCoefficientAction

universe u v

variable {r : ℕ} {U : Type u} {A : Type v} [CommGroup U] [CommGroup A]

/-- The normalized cocycle defined by the twisted diagonal pairing. -/
def torusCocycle (H : U →* U →* A) (c : ℤ) : CentralTwoCocycle (Fin r → U) A :=
  CentralTwoCocycle.ofBilinear (torusPairing H c)

/-- The central extension in the diagonal coordinates of Kazhdan–Patterson. -/
abbrev TorusCover (H : U →* U →* A) (c : ℤ) :=
  (torusCocycle (r := r) H c).Extension

@[simp]
theorem torusCocycle_apply (H : U →* U →* A) (c : ℤ) (t s : Fin r → U) :
    torusCocycle H c (t, s) = torusPairing H c t s := rfl

/-- The ratio of the diagonal pairing to its transpose. -/
def torusCommutatorPairing (H : U →* U →* A) (c : ℤ) :
    (Fin r → U) →* (Fin r → U) →* A :=
  torusPairing H c / (torusPairing H c).flip

theorem torusCommutatorPairing_apply (H : U →* U →* A) (c : ℤ) (t s : Fin r → U) :
    torusCommutatorPairing H c t s = torusPairing H c t s / torusPairing H c s t := rfl

theorem torusCover_commutator (H : U →* U →* A) (c : ℤ)
    (x y : TorusCover (r := r) H c) :
    ⁅x, y⁆ = inl (torusCocycle H c) (torusCommutatorPairing H c x.right y.right) := by
  let b := torusCommutatorPairing H c x.right y.right
  have hxy : x * y = inl (torusCocycle H c) b * (y * x) := by
    apply NormalizedTwoCocycle.Extension.ext
    · simp only [NormalizedTwoCocycle.Extension.mul_left,
        NormalizedTwoCocycle.Extension.inl_left, NormalizedTwoCocycle.Extension.inl_right,
        NormalizedTwoCocycle.one_left, mul_one]
      change x.left * y.left * torusPairing H c x.right y.right =
        b * (y.left * x.left * torusPairing H c y.right x.right)
      calc
        _ = (b * torusPairing H c y.right x.right) * (y.left * x.left) := by
          change _ = (torusCommutatorPairing H c x.right y.right *
            torusPairing H c y.right x.right) * (y.left * x.left)
          rw [torusCommutatorPairing_apply, div_mul_cancel]
          ac_rfl
        _ = _ := by ac_rfl
    · simp [mul_comm]
  change ⁅x, y⁆ = inl (torusCocycle H c) b
  calc
    ⁅x, y⁆ = (x * y) * (y * x)⁻¹ := by rw [commutatorElement_def, mul_inv_rev, mul_assoc]
    _ = inl (torusCocycle H c) b := by rw [hxy, mul_inv_cancel_right]

theorem torusCover_mem_center_iff (H : U →* U →* A) (c : ℤ)
    (x : TorusCover (r := r) H c) :
    x ∈ Subgroup.center (TorusCover (r := r) H c) ↔
      ∀ s, torusCommutatorPairing H c x.right s = 1 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hx s
    have h := commutatorElement_eq_one_iff_mul_comm.mpr (hx (sectionMap (torusCocycle H c) s)).symm
    rw [torusCover_commutator, NormalizedTwoCocycle.Extension.sectionMap_right, ← map_one (inl _)]
      at h
    exact NormalizedTwoCocycle.Extension.inl_injective _ h
  · intro hx y
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [torusCover_commutator, hx, map_one]

private theorem prod_off_diagonal (H : U →* U →* A) (t s : Fin r → U) :
    (∏ p ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 ≠ p.2),
      H (t p.1) (s p.2)) =
      H (diagonalDeterminant t) (diagonalDeterminant s) / ∏ i, H (t i) (s i) := by
  apply eq_div_iff_mul_eq'.mpr
  have hdiag :
      (∏ p ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => ¬ p.1 ≠ p.2),
        H (t p.1) (s p.2)) = ∏ i, H (t i) (s i) := by
    refine Finset.prod_nbij' Prod.fst (fun i => (i, i)) (by simp) (by simp) ?_ (by simp) ?_
    · intro p hp
      have he : p.1 = p.2 := by simpa using hp
      exact Prod.ext rfl he
    · intro p hp
      have he : p.1 = p.2 := by simpa using hp
      rw [he]
  rw [← hdiag, Finset.prod_filter_mul_prod_filter_not, Fintype.prod_prod_type,
    diagonalDeterminant_apply, diagonalDeterminant_apply, map_prod]
  simp only [MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_comm

/-- The commutator in determinant and diagonal coordinates for a skew-symmetric symbol.
Inversion under exchange of arguments suffices, including for symbols with nontrivial
self-pairings. -/
theorem torusCommutatorPairing_eq (H : U →* U →* A)
    (hskew : ∀ a b, H b a = (H a b)⁻¹) (c : ℤ) (t s : Fin r → U) :
    torusCommutatorPairing H c t s =
      H (diagonalDeterminant t) (diagonalDeterminant s) ^ (2 * c + 1) /
        ∏ i, H (t i) (s i) := by
  let upper := (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 < p.2)
  let lower := (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.2 < p.1)
  let f (p : Fin r × Fin r) := H (t p.1) (s p.2)
  let d := H (diagonalDeterminant t) (diagonalDeterminant s)
  have hswap : (∏ p ∈ upper, H (s p.1) (t p.2)) = (∏ p ∈ lower, f p)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_equiv (Equiv.prodComm _ _) (by simp [upper, lower])
      (fun p _ => hskew (t p.2) (s p.1))
  have hunion : upper ∪ lower =
        (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 ≠ p.2) := by
    ext p
    simp only [upper, lower, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ne_iff_lt_or_gt.symm
  have hdisj : Disjoint upper lower := by
    refine Finset.disjoint_left.mpr (fun p hp hq => ?_)
    exact lt_asymm (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  rw [torusCommutatorPairing_apply, torusPairing_apply, torusPairing_apply,
    ← diagonalDeterminant_apply, ← diagonalDeterminant_apply]
  change (∏ p ∈ upper, f p) * d ^ c /
      ((∏ p ∈ upper, H (s p.1) (t p.2)) *
        H (diagonalDeterminant s) (diagonalDeterminant t) ^ c) =
        d ^ (2 * c + 1) / ∏ i, H (t i) (s i)
  rw [hswap, hskew (diagonalDeterminant t) (diagonalDeterminant s), inv_zpow,
    div_eq_mul_inv, mul_inv, inv_inv, inv_inv]
  calc
    _ = ((∏ p ∈ upper, f p) * (∏ p ∈ lower, f p)) * (d ^ c * d ^ c) := by ac_rfl
    _ = (d / ∏ i, H (t i) (s i)) * d ^ (2 * c) := by
      rw [← Finset.prod_union hdisj, hunion, prod_off_diagonal, ← zpow_add, two_mul]
    _ = _ := by
      rw [zpow_add, zpow_one, div_eq_mul_inv, div_eq_mul_inv]
      ac_rfl

end Langlands.KazhdanPatterson
