import Langlands.LinearAlgebra.StableEndomorphismQuotientStatements

/-!
# Kernels, images and exactness of the successive quotient maps

Proofs of the ten assertions `PowerQuotientExactnessAt t k` for Renard 2026,
Appendix C.II, proof of Lemma (iv), printed page 278 / PDF page 284, and of the
aggregate `PowerQuotientExactSequenceStatements`.

The coefficient ring is arbitrary, the module is arbitrary and every natural index,
including `k = 0`, is allowed. No finiteness or stabilization hypothesis is used.
-/

set_option autoImplicit false

universe uR uV

namespace Langlands.LinearAlgebra.StableEndomorphism

variable {R : Type uR} {V : Type uV} [Ring R] [AddCommGroup V] [Module R V]
variable (t : Module.End R V)

section Ambient

/-! Identities between submodules and memberships in the ambient module `V`. -/

variable {t}

/-- `t (t ^ k x) = t ^ (k + 1) x`. -/
theorem apply_pow_apply (k : ℕ) (x : V) : t ((t ^ k) x) = (t ^ (k + 1)) x := by
  rw [pow_succ', Module.End.mul_apply]

/-- `t ^ k (t x) = t ^ (k + 1) x`. -/
theorem pow_apply_apply (k : ℕ) (x : V) : (t ^ k) (t x) = (t ^ (k + 1)) x := by
  rw [pow_succ, Module.End.mul_apply]

variable (t)

/-- `t (N_(j+1)) = Im t ∩ N_j`. -/
theorem map_kerPow_succ (j : ℕ) :
    (kerPow t (j + 1)).map t = LinearMap.range t ⊓ kerPow t j := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self t x, apply_mem_kerPow hx⟩
  · rintro ⟨hy, hyj⟩
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    refine Submodule.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [mem_kerPow, ← pow_apply_apply]
    exact mem_kerPow.mp hyj

variable {t}

/-- For `x ∈ N_(k+1)`, `t ^ k x ∈ I_(k+1)` iff `x ∈ N_k + (Im t ∩ N_(k+1))`. -/
theorem pow_apply_mem_rangePow_succ_iff {k : ℕ} {x : V} (hx : x ∈ kerPow t (k + 1)) :
    (t ^ k) x ∈ rangePow t (k + 1) ↔
      x ∈ kerPow t k ⊔ (LinearMap.range t ⊓ kerPow t (k + 1)) := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := mem_rangePow.mp h
    have hxy : x - t y ∈ kerPow t k := by
      rw [mem_kerPow, map_sub, pow_apply_apply, hy, sub_self]
    have hty : t y ∈ kerPow t (k + 1) := by
      have h' := sub_mem hx (kerPow_le_succ t k hxy)
      rwa [sub_sub_cancel] at h'
    exact Submodule.mem_sup.mpr
      ⟨x - t y, hxy, t y, Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self t y, hty⟩,
        sub_add_cancel x (t y)⟩
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp h
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp (Submodule.mem_inf.mp hb).1
    refine mem_rangePow.mpr ⟨c, ?_⟩
    rw [map_add, mem_kerPow.mp ha, zero_add, pow_apply_apply]

/-- For `w ∈ I_k`, `t w ∈ I_(k+2)` iff `w ∈ I_(k+1) + t ^ k (N_(k+1))`. -/
theorem apply_mem_rangePow_succ_succ_iff {k : ℕ} {w : V} (hw : w ∈ rangePow t k) :
    t w ∈ rangePow t (k + 2) ↔
      w ∈ rangePow t (k + 1) ⊔ (kerPow t (k + 1)).map (t ^ k) := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := mem_rangePow.mp hw
    obtain ⟨z, hz⟩ := mem_rangePow.mp h
    have hxz : x - t z ∈ kerPow t (k + 1) := by
      have e1 : (t ^ (k + 1)) x = t ((t ^ k) x) := (apply_pow_apply k x).symm
      have e2 : (t ^ (k + 1)) (t z) = (t ^ (k + 2)) z := pow_apply_apply (k + 1) z
      rw [mem_kerPow, map_sub, e1, e2, hz, sub_self]
    refine Submodule.mem_sup.mpr
      ⟨(t ^ (k + 1)) z, LinearMap.mem_range_self _ z, (t ^ k) (x - t z),
        Submodule.mem_map_of_mem hxz, ?_⟩
    rw [map_sub, pow_apply_apply, add_sub_cancel]
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp h
    obtain ⟨c, rfl⟩ := mem_rangePow.mp ha
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hb
    refine mem_rangePow.mpr ⟨c, ?_⟩
    rw [map_add, apply_pow_apply, apply_pow_apply, mem_kerPow.mp hx, add_zero]

end Ambient

section Images

/-! Membership of a class in the image of an ambient submodule containing the
denominator. -/

variable {t}

/-- Equality of classes in `E_k = N_(k+1) / N_k`. -/
theorem kerQuotientMk_eq_iff {k : ℕ} {x y : kerPow t (k + 1)} :
    kerQuotientMk t k x = kerQuotientMk t k y ↔ (x : V) - y ∈ kerPow t k := by
  rw [kerQuotientMk_apply, kerQuotientMk_apply, Submodule.Quotient.eq, mem_kerPowInSucc,
    Submodule.coe_sub]

/-- Equality of classes in `F_k = I_k / I_(k+1)`. -/
theorem rangeQuotientMk_eq_iff {k : ℕ} {x y : rangePow t k} :
    rangeQuotientMk t k x = rangeQuotientMk t k y ↔ (x : V) - y ∈ rangePow t (k + 1) := by
  rw [rangeQuotientMk_apply, rangeQuotientMk_apply, Submodule.Quotient.eq,
    mem_rangePowSuccIn, Submodule.coe_sub]

/-- If `N_k ≤ S`, the class of `x ∈ N_(k+1)` lies in the image of `S` in `E_k` iff
`x ∈ S`. -/
theorem kerQuotientMk_mem_map_comap_iff {k : ℕ} {S : Submodule R V} (hS : kerPow t k ≤ S)
    (x : kerPow t (k + 1)) :
    kerQuotientMk t k x ∈ (S.comap (kerPow t (k + 1)).subtype).map (kerQuotientMk t k) ↔
      (x : V) ∈ S := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h := hS (kerQuotientMk_eq_iff.mp hyx)
    have h' := sub_mem (show (y : V) ∈ S from hy) h
    rwa [sub_sub_cancel] at h'
  · intro hx
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

/-- If `I_(k+1) ≤ S`, the class of `w ∈ I_k` lies in the image of `S` in `F_k` iff
`w ∈ S`. -/
theorem rangeQuotientMk_mem_map_comap_iff {k : ℕ} {S : Submodule R V}
    (hS : rangePow t (k + 1) ≤ S) (w : rangePow t k) :
    rangeQuotientMk t k w ∈ (S.comap (rangePow t k).subtype).map (rangeQuotientMk t k) ↔
      (w : V) ∈ S := by
  constructor
  · rintro ⟨y, hy, hyw⟩
    have h := hS (rangeQuotientMk_eq_iff.mp hyw)
    have h' := sub_mem (show (y : V) ∈ S from hy) h
    rwa [sub_sub_cancel] at h'
  · intro hw
    exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩

end Images

section Clauses

/-- Clause 1: the composite `N_(k+2) → N_(k+1) → E_k` has kernel exactly `N_(k+1)`. -/
theorem ker_kerShiftMk (k : ℕ) : LinearMap.ker (kerShiftMk t k) = kerPowInSucc t (k + 1) := by
  ext x
  rw [LinearMap.mem_ker, kerShiftMk_apply, kerQuotientMk_eq_zero_iff, coe_kerShift_apply,
    mem_kerPowInSucc, mem_kerPow, mem_kerPow, pow_apply_apply]

/-- Clause 2: `ker (E_k → F_k) = (N_k + (Im t ∩ N_(k+1))) / N_k`. -/
theorem ker_kerToRangeQuotient (k : ℕ) :
    LinearMap.ker (kerToRangeQuotient t k) =
      ((kerPow t k ⊔ (LinearMap.range t ⊓ kerPow t (k + 1))).comap
        (kerPow t (k + 1)).subtype).map (kerQuotientMk t k) := by
  ext y
  obtain ⟨x, rfl⟩ := kerQuotientMk_surjective t k y
  rw [kerQuotientMk_mem_map_comap_iff le_sup_left, LinearMap.mem_ker, kerToRangeQuotient_mk,
    rangeQuotientMk_eq_zero_iff, coe_kerToRange_apply]
  exact pow_apply_mem_rangePow_succ_iff x.2

/-- Clause 3: `Im (E_k → F_k) = (I_(k+1) + t ^ k (N_(k+1))) / I_(k+1)`. -/
theorem range_kerToRangeQuotient (k : ℕ) :
    LinearMap.range (kerToRangeQuotient t k) =
      ((rangePow t (k + 1) ⊔ (kerPow t (k + 1)).map (t ^ k)).comap
        (rangePow t k).subtype).map (rangeQuotientMk t k) := by
  ext y
  obtain ⟨w, rfl⟩ := rangeQuotientMk_surjective t k y
  rw [rangeQuotientMk_mem_map_comap_iff le_sup_left, LinearMap.mem_range]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨x, rfl⟩ := kerQuotientMk_surjective t k e
    rw [kerToRangeQuotient_mk] at he
    have h : (t ^ k) (x : V) - w ∈ rangePow t (k + 1) := rangeQuotientMk_eq_iff.mp he
    refine Submodule.mem_sup.mpr
      ⟨(w : V) - (t ^ k) x, ?_, (t ^ k) x, Submodule.mem_map_of_mem x.2, sub_add_cancel _ _⟩
    rw [← neg_sub]
    exact neg_mem h
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hb
    refine ⟨kerQuotientMk t k ⟨x, hx⟩, ?_⟩
    rw [kerToRangeQuotient_mk]
    refine rangeQuotientMk_eq_iff.mpr ?_
    show (t ^ k) x - (w : V) ∈ rangePow t (k + 1)
    rw [← hab, sub_add_cancel_right]
    exact neg_mem ha

/-- Clause 4: the arrow `E_(k+1) → E_k` is injective. -/
theorem kerQuotientShift_injective (k : ℕ) : Function.Injective (kerQuotientShift t k) := by
  rw [← LinearMap.ker_eq_bot, kerQuotientShift]
  exact Submodule.ker_liftQ_eq_bot _ _ _ (ker_kerShiftMk t k).le

/-- Clause 6: `Im (E_(k+1) → E_k) = (N_k + (Im t ∩ N_(k+1))) / N_k`. -/
theorem range_kerQuotientShift (k : ℕ) :
    LinearMap.range (kerQuotientShift t k) =
      ((kerPow t k ⊔ (LinearMap.range t ⊓ kerPow t (k + 1))).comap
        (kerPow t (k + 1)).subtype).map (kerQuotientMk t k) := by
  ext y
  obtain ⟨x, rfl⟩ := kerQuotientMk_surjective t k y
  rw [kerQuotientMk_mem_map_comap_iff le_sup_left, LinearMap.mem_range]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨z, rfl⟩ := kerQuotientMk_surjective t (k + 1) e
    rw [kerQuotientShift_mk] at he
    have h : t (z : V) - x ∈ kerPow t k := kerQuotientMk_eq_iff.mp he
    refine Submodule.mem_sup.mpr
      ⟨(x : V) - t z, ?_, t z,
        Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self t z, apply_mem_kerPow z.2⟩,
        sub_add_cancel _ _⟩
    rw [← neg_sub]
    exact neg_mem h
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
    obtain ⟨hbr, hbk⟩ := Submodule.mem_inf.mp hb
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hbr
    have hc : c ∈ kerPow t (k + 2) := by
      rw [mem_kerPow, ← pow_apply_apply]
      exact mem_kerPow.mp hbk
    refine ⟨kerQuotientMk t (k + 1) ⟨c, hc⟩, ?_⟩
    rw [kerQuotientShift_mk]
    refine kerQuotientMk_eq_iff.mpr ?_
    show t c - (x : V) ∈ kerPow t k
    rw [← hab, sub_add_cancel_right]
    exact neg_mem ha

/-- Clause 5: `Im (E_(k+1) → E_k) = (N_k + t (N_(k+2))) / N_k`, with the corrected
index `k + 2`. -/
theorem range_kerQuotientShift_eq_map (k : ℕ) :
    LinearMap.range (kerQuotientShift t k) =
      ((kerPow t k ⊔ (kerPow t (k + 2)).map t).comap
        (kerPow t (k + 1)).subtype).map (kerQuotientMk t k) := by
  rw [map_kerPow_succ t (k + 1)]
  exact range_kerQuotientShift t k

/-- Clause 7: the arrow `F_k → F_(k+1)` is surjective. -/
theorem rangeQuotientShift_surjective (k : ℕ) : Function.Surjective (rangeQuotientShift t k) := by
  intro y
  obtain ⟨w, rfl⟩ := rangeQuotientMk_surjective t (k + 1) y
  obtain ⟨v, hv⟩ := mem_rangePow.mp w.2
  refine ⟨rangeQuotientMk t k ⟨(t ^ k) v, pow_apply_mem_rangePow k v⟩, ?_⟩
  rw [rangeQuotientShift_mk]
  congr 1
  apply Subtype.ext
  show t ((t ^ k) v) = w
  rw [apply_pow_apply, hv]

/-- Clause 8: `ker (F_k → F_(k+1)) = (I_(k+1) + t ^ k (N_(k+1))) / I_(k+1)`. -/
theorem ker_rangeQuotientShift (k : ℕ) :
    LinearMap.ker (rangeQuotientShift t k) =
      ((rangePow t (k + 1) ⊔ (kerPow t (k + 1)).map (t ^ k)).comap
        (rangePow t k).subtype).map (rangeQuotientMk t k) := by
  ext y
  obtain ⟨w, rfl⟩ := rangeQuotientMk_surjective t k y
  rw [rangeQuotientMk_mem_map_comap_iff le_sup_left, LinearMap.mem_ker, rangeQuotientShift_mk,
    rangeQuotientMk_eq_zero_iff, coe_rangeShift_apply]
  exact apply_mem_rangePow_succ_succ_iff w.2

/-- Clause 9: exactness at `E_k`. -/
theorem range_kerQuotientShift_eq_ker (k : ℕ) :
    LinearMap.range (kerQuotientShift t k) = LinearMap.ker (kerToRangeQuotient t k) :=
  (range_kerQuotientShift t k).trans (ker_kerToRangeQuotient t k).symm

/-- Clause 10: exactness at `F_k`. -/
theorem range_kerToRangeQuotient_eq_ker (k : ℕ) :
    LinearMap.range (kerToRangeQuotient t k) = LinearMap.ker (rangeQuotientShift t k) :=
  (range_kerToRangeQuotient t k).trans (ker_rangeQuotientShift t k).symm

/-- All ten assertions, for every ring, module, endomorphism and natural index. -/
theorem powerQuotientExactnessAt (k : ℕ) : PowerQuotientExactnessAt t k :=
  ⟨ker_kerShiftMk t k, ker_kerToRangeQuotient t k, range_kerToRangeQuotient t k,
    kerQuotientShift_injective t k, range_kerQuotientShift_eq_map t k,
    range_kerQuotientShift t k, rangeQuotientShift_surjective t k, ker_rangeQuotientShift t k,
    range_kerQuotientShift_eq_ker t k, range_kerToRangeQuotient_eq_ker t k⟩

end Clauses

section Aggregate

/-- The ring-general closed target. -/
theorem powerQuotientExactSequenceStatement : PowerQuotientExactSequenceStatement.{uR, uV} :=
  fun _ _ _ _ _ t k => powerQuotientExactnessAt t k

/-- The complex target, as the specialization of the ring-general one at `R := ℂ`. -/
theorem complexPowerQuotientExactSequenceStatement :
    ComplexPowerQuotientExactSequenceStatement.{uV} :=
  fun V _ _ t k => powerQuotientExactSequenceStatement.{0, uV} ℂ V t k

/-- The aggregate target. -/
theorem powerQuotientExactSequenceStatements : PowerQuotientExactSequenceStatements.{uR, uV} :=
  ⟨powerQuotientExactSequenceStatement, complexPowerQuotientExactSequenceStatement⟩

end Aggregate

end Langlands.LinearAlgebra.StableEndomorphism
