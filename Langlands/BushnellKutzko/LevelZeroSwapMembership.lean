import Langlands.BushnellKutzko.LevelZeroSwap
import Langlands.BushnellKutzko.LevelZeroResidue

/-! # Membership of two-block elements in the standard unit groups -/

open Matrix ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF

variable {F : Type uF} [Field F] {e f : ℕ}

theorem pairEmb_forall {i j : Fin e} (hij : i ≠ j) (M : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F)
    (P : Fin f × Fin e → Fin f × Fin e → F → Prop)
    (hll : ∀ a b, P (a, i) (b, i) (M (.inl a) (.inl b)))
    (hlr : ∀ a b, P (a, i) (b, j) (M (.inl a) (.inr b)))
    (hrl : ∀ a b, P (a, j) (b, i) (M (.inr a) (.inl b)))
    (hrr : ∀ a b, P (a, j) (b, j) (M (.inr a) (.inr b)))
    (hrest : ∀ p q : Fin f × Fin e, ((p.2 ≠ i ∧ p.2 ≠ j) ∨ (q.2 ≠ i ∧ q.2 ≠ j)) →
      P p q ((1 : Matrix (Fin f × Fin e) (Fin f × Fin e) F) p q)) :
    ∀ p q, P p q (pairEmb F hij M p q) := by
  rintro ⟨a, k⟩ ⟨b, l⟩
  rcases eq_or_ne k i with rfl | hki
  · rcases eq_or_ne l k with rfl | hlk
    · simpa using hll a b
    · rcases eq_or_ne l j with rfl | hlj
      · simpa using hlr a b
      · rw [pairEmb_rest_right hij M _ _ hlk hlj]
        exact hrest _ _ (Or.inr ⟨hlk, hlj⟩)
  · rcases eq_or_ne k j with rfl | hkj
    · rcases eq_or_ne l i with rfl | hli
      · simpa using hrl a b
      · rcases eq_or_ne l k with rfl | hlk
        · simpa using hrr a b
        · rw [pairEmb_rest_right hij M _ _ hli hlk]
          exact hrest _ _ (Or.inr ⟨hli, hlk⟩)
    · rw [pairEmb_rest_left hij M _ _ hki hkj]
      exact hrest _ _ (Or.inl ⟨hki, hkj⟩)

variable [ValuativeRel F]

private theorem val_one_apply_le {ι : Type*} [DecidableEq ι] (p q : ι) :
    valuation F ((1 : Matrix ι ι F) p q) ≤ 1 := by
  by_cases h : p = q
  · subst h
    rw [Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, map_zero]
    exact zero_le

theorem pairEmb_inOrd {i j : Fin e} (hij : i < j) (M : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F)
    (h11 : ∀ a b, valuation F (M (.inl a) (.inl b)) ≤ 1)
    (h12 : ∀ a b, valuation F (M (.inl a) (.inr b)) < 1)
    (h21 : ∀ a b, valuation F (M (.inr a) (.inl b)) ≤ 1)
    (h22 : ∀ a b, valuation F (M (.inr a) (.inr b)) ≤ 1) :
    InOrd (pairEmb F hij.ne M) := by
  intro p q
  refine pairEmb_forall hij.ne M
    (fun p q x => valuation F x ≤ 1 ∧ (p.2 < q.2 → valuation F x < 1))
    (fun a b => ⟨h11 a b, fun h => absurd h (lt_irrefl _)⟩)
    (fun a b => ⟨(h12 a b).le, fun _ => h12 a b⟩)
    (fun a b => ⟨h21 a b, fun h => absurd h (not_lt.mpr hij.le)⟩)
    (fun a b => ⟨h22 a b, fun h => absurd h (lt_irrefl _)⟩)
    (fun p q _ => ⟨val_one_apply_le p q, fun h => by
      rw [Matrix.one_apply_ne (fun hpq => by rw [hpq] at h; exact lt_irrefl _ h)]
      simp⟩) p q

theorem pairEmb_sub_one_inRad {i j : Fin e} (hij : i < j)
    (M : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F)
    (h11 : ∀ a b, valuation F (M (.inl a) (.inl b) - (1 : Matrix (Fin f) (Fin f) F) a b) < 1)
    (h12 : ∀ a b, valuation F (M (.inl a) (.inr b)) < 1)
    (h21 : ∀ a b, valuation F (M (.inr a) (.inl b)) ≤ 1)
    (h22 : ∀ a b, valuation F (M (.inr a) (.inr b) - (1 : Matrix (Fin f) (Fin f) F) a b) < 1) :
    InRad (pairEmb F hij.ne M - 1) := by
  intro p q
  rw [Matrix.sub_apply]
  refine pairEmb_forall hij.ne M
    (fun p q x => valuation F (x - (1 : Matrix (Fin f × Fin e) (Fin f × Fin e) F) p q) ≤ 1 ∧
      (p.2 ≤ q.2 → valuation F (x - (1 : Matrix (Fin f × Fin e) (Fin f × Fin e) F) p q) < 1))
    (fun a b => ?_) (fun a b => ?_) (fun a b => ?_) (fun a b => ?_)
    (fun p q _ => by simp) p q
  · have h1 : (1 : Matrix (Fin f × Fin e) (Fin f × Fin e) F) (a, i) (b, i) =
        (1 : Matrix (Fin f) (Fin f) F) a b := by
      by_cases hab : a = b
      · subst hab; simp
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (fun h => hab (congrArg Prod.fst h))]
    rw [h1]
    exact ⟨(h11 a b).le, fun _ => h11 a b⟩
  · rw [Matrix.one_apply_ne (fun h => hij.ne (congrArg Prod.snd h)), sub_zero]
    exact ⟨(h12 a b).le, fun _ => h12 a b⟩
  · rw [Matrix.one_apply_ne (fun h => hij.ne (congrArg Prod.snd h).symm), sub_zero]
    exact ⟨h21 a b, fun h => absurd h (not_le.mpr hij)⟩
  · have h1 : (1 : Matrix (Fin f × Fin e) (Fin f × Fin e) F) (a, j) (b, j) =
        (1 : Matrix (Fin f) (Fin f) F) a b := by
      by_cases hab : a = b
      · subst hab; simp
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (fun h => hab (congrArg Prod.fst h))]
    rw [h1]
    exact ⟨(h22 a b).le, fun _ => h22 a b⟩

/-- Block conditions for `U^1` of a `2 × 2` block matrix on two consecutive blocks. -/
def Is2Rad (M : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F) : Prop :=
  (∀ a b, valuation F (M (.inl a) (.inl b) - (1 : Matrix (Fin f) (Fin f) F) a b) < 1) ∧
    (∀ a b, valuation F (M (.inl a) (.inr b)) < 1) ∧
    (∀ a b, valuation F (M (.inr a) (.inl b)) ≤ 1) ∧
    (∀ a b, valuation F (M (.inr a) (.inr b) - (1 : Matrix (Fin f) (Fin f) F) a b) < 1)

/-- Block conditions for `U(𝔄)` of a `2 × 2` block matrix on two consecutive blocks. -/
def Is2Ord (M : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F) : Prop :=
  (∀ a b, valuation F (M (.inl a) (.inl b)) ≤ 1) ∧
    (∀ a b, valuation F (M (.inl a) (.inr b)) < 1) ∧
    (∀ a b, valuation F (M (.inr a) (.inl b)) ≤ 1) ∧
    (∀ a b, valuation F (M (.inr a) (.inr b)) ≤ 1)

theorem pairGL_mem_J1 {i j : Fin e} (hij : i < j) {u : GL (Fin f ⊕ Fin f) F}
    (hu : Is2Rad (u : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F))
    (hu' : Is2Rad ((u⁻¹ : GL (Fin f ⊕ Fin f) F) : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F)) :
    pairGL hij.ne u ∈ J1 F e f := by
  refine mem_J1_of_inRad ?_ ?_
  · exact pairEmb_sub_one_inRad hij _ hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
  · rw [← map_inv]
    exact pairEmb_sub_one_inRad hij _ hu'.1 hu'.2.1 hu'.2.2.1 hu'.2.2.2

theorem pairGL_mem_J0 {i j : Fin e} (hij : i < j) {u : GL (Fin f ⊕ Fin f) F}
    (hu : Is2Ord (u : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F))
    (hu' : Is2Ord ((u⁻¹ : GL (Fin f ⊕ Fin f) F) : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F)) :
    pairGL hij.ne u ∈ J0 F e f := by
  refine mem_J0_of_inOrd ?_ ?_
  · exact pairEmb_inOrd hij _ hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
  · rw [← map_inv]
    exact pairEmb_inOrd hij _ hu'.1 hu'.2.1 hu'.2.2.1 hu'.2.2.2

omit [ValuativeRel F] in
theorem lowerU_inv (Y : Matrix (Fin f) (Fin f) F) : (lowerU Y)⁻¹ = lowerU (-Y) := by
  refine inv_eq_of_mul_eq_one_right ?_
  ext1
  simp [fromBlocks_multiply]

omit [ValuativeRel F] in
theorem upperU_inv (X : Matrix (Fin f) (Fin f) F) : (upperU X)⁻¹ = upperU (-X) := by
  refine inv_eq_of_mul_eq_one_right ?_
  ext1
  simp [fromBlocks_multiply]

omit [ValuativeRel F] in
theorem diagU_inv (A D : GL (Fin f) F) : (diagU A D)⁻¹ = diagU A⁻¹ D⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  ext1
  simp [fromBlocks_multiply]

private theorem one_sub_one (a b : Fin f) :
    valuation F ((1 : Matrix (Fin f) (Fin f) F) a b - (1 : Matrix (Fin f) (Fin f) F) a b) < 1 := by
  simp

theorem is2Rad_lowerU {Y : Matrix (Fin f) (Fin f) F} (hY : ∀ a b, valuation F (Y a b) ≤ 1) :
    Is2Rad ((lowerU Y : GL (Fin f ⊕ Fin f) F) : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F) :=
  ⟨fun a b => by simp, fun a b => by simp, fun a b => by simpa using hY a b, fun a b => by simp⟩

theorem is2Rad_upperU {X : Matrix (Fin f) (Fin f) F} (hX : ∀ a b, valuation F (X a b) < 1) :
    Is2Rad ((upperU X : GL (Fin f ⊕ Fin f) F) : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F) :=
  ⟨fun a b => by simp, fun a b => by simpa using hX a b, fun a b => by simp, fun a b => by simp⟩

/-- A lower unipotent element with integral block lies in `U^1(𝔄)`. -/
theorem lowerU_mem_J1 {i j : Fin e} (hij : i < j) {Y : Matrix (Fin f) (Fin f) F}
    (hY : ∀ a b, valuation F (Y a b) ≤ 1) : pairGL hij.ne (lowerU Y) ∈ J1 F e f :=
  pairGL_mem_J1 hij (is2Rad_lowerU hY)
    (by rw [lowerU_inv]; exact is2Rad_lowerU fun a b => by simpa using hY a b)

/-- An upper unipotent element with block in the maximal ideal lies in `U^1(𝔄)`. -/
theorem upperU_mem_J1 {i j : Fin e} (hij : i < j) {X : Matrix (Fin f) (Fin f) F}
    (hX : ∀ a b, valuation F (X a b) < 1) : pairGL hij.ne (upperU X) ∈ J1 F e f :=
  pairGL_mem_J1 hij (is2Rad_upperU hX)
    (by rw [upperU_inv]; exact is2Rad_upperU fun a b => by simpa using hX a b)

/-- Integral invertible matrices whose inverses are integral. -/
def IsIntGL (A : GL (Fin f) F) : Prop :=
  (∀ a b, valuation F ((A : Matrix (Fin f) (Fin f) F) a b) ≤ 1) ∧
    ∀ a b, valuation F (((A⁻¹ : GL (Fin f) F) : Matrix (Fin f) (Fin f) F) a b) ≤ 1

theorem IsIntGL.inv {A : GL (Fin f) F} (hA : IsIntGL A) : IsIntGL A⁻¹ :=
  ⟨hA.2, by simpa using hA.1⟩

/-- A block diagonal element with integral blocks lies in `U(𝔄)`. -/
theorem diagU_mem_J0 {i j : Fin e} (hij : i < j) {A D : GL (Fin f) F} (hA : IsIntGL A)
    (hD : IsIntGL D) : pairGL hij.ne (diagU A D) ∈ J0 F e f :=
  pairGL_mem_J0 hij ⟨fun a b => by simpa using hA.1 a b, fun a b => by simp,
      fun a b => by simp, fun a b => by simpa using hD.1 a b⟩
    (by
      rw [diagU_inv]
      exact ⟨fun a b => by simpa using hA.2 a b, fun a b => by simp,
        fun a b => by simp, fun a b => by simpa using hD.2 a b⟩)

end Langlands.BushnellKutzko.LevelZero
