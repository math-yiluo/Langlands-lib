import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Data.Matrix.Block

/-! # The standard principal order of period `e` with blocks of size `f`

Matrices are indexed by `Fin f × Fin e`, the second coordinate being the block, as in
Mathlib's `Matrix.blockDiagonal`. -/

open ValuativeRel Matrix

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] {e f : ℕ}

/-- Indices of the standard block decomposition. -/
abbrev Ix (e f : ℕ) := Fin f × Fin e

/-- The standard principal order: integral entries, and entries of the blocks strictly above
the block diagonal in the maximal ideal. -/
def InOrd (x : Matrix (Ix e f) (Ix e f) F) : Prop :=
  ∀ p q : Ix e f, valuation F (x p q) ≤ 1 ∧ (p.2 < q.2 → valuation F (x p q) < 1)

/-- Its Jacobson radical: integral entries, and entries of the blocks on and above the block
diagonal in the maximal ideal. -/
def InRad (x : Matrix (Ix e f) (Ix e f) F) : Prop :=
  ∀ p q : Ix e f, valuation F (x p q) ≤ 1 ∧ (p.2 ≤ q.2 → valuation F (x p q) < 1)

theorem InRad.inOrd {x : Matrix (Ix e f) (Ix e f) F} (h : InRad x) : InOrd x :=
  fun p q => ⟨(h p q).1, fun hpq => (h p q).2 hpq.le⟩

theorem inOrd_one : InOrd (1 : Matrix (Ix e f) (Ix e f) F) := by
  intro p q
  by_cases hpq : p = q
  · subst hpq
    simp
  · simp [Matrix.one_apply_ne hpq]

theorem inRad_zero : InRad (0 : Matrix (Ix e f) (Ix e f) F) := by
  intro p q
  simp

private theorem val_mul_lt_one_left {a b : F} (ha : valuation F a < 1) (hb : valuation F b ≤ 1) :
    valuation F (a * b) < 1 := by
  rw [map_mul]
  calc valuation F a * valuation F b ≤ valuation F a * 1 := mul_le_mul' le_rfl hb
    _ < 1 := by rwa [mul_one]

private theorem val_mul_lt_one_right {a b : F} (ha : valuation F a ≤ 1) (hb : valuation F b < 1) :
    valuation F (a * b) < 1 := by
  rw [mul_comm]
  exact val_mul_lt_one_left hb ha

private theorem val_mul_le_one {a b : F} (ha : valuation F a ≤ 1) (hb : valuation F b ≤ 1) :
    valuation F (a * b) ≤ 1 := by
  rw [map_mul]
  exact mul_le_one' ha hb

theorem InOrd.add {x y : Matrix (Ix e f) (Ix e f) F} (hx : InOrd x) (hy : InOrd y) :
    InOrd (x + y) := fun p q =>
  ⟨Valuation.map_add_le _ (hx p q).1 (hy p q).1,
    fun h => Valuation.map_add_lt _ ((hx p q).2 h) ((hy p q).2 h)⟩

theorem InRad.add {x y : Matrix (Ix e f) (Ix e f) F} (hx : InRad x) (hy : InRad y) :
    InRad (x + y) := fun p q =>
  ⟨Valuation.map_add_le _ (hx p q).1 (hy p q).1,
    fun h => Valuation.map_add_lt _ ((hx p q).2 h) ((hy p q).2 h)⟩

theorem InRad.neg {x : Matrix (Ix e f) (Ix e f) F} (hx : InRad x) : InRad (-x) := fun p q => by
  simpa [Valuation.map_neg] using hx p q

theorem InOrd.neg {x : Matrix (Ix e f) (Ix e f) F} (hx : InOrd x) : InOrd (-x) := fun p q => by
  simpa [Valuation.map_neg] using hx p q

theorem InRad.sub {x y : Matrix (Ix e f) (Ix e f) F} (hx : InRad x) (hy : InRad y) :
    InRad (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem InOrd.sub {x y : Matrix (Ix e f) (Ix e f) F} (hx : InOrd x) (hy : InOrd y) :
    InOrd (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem InOrd.mul {x y : Matrix (Ix e f) (Ix e f) F} (hx : InOrd x) (hy : InOrd y) :
    InOrd (x * y) := by
  intro p q
  refine ⟨?_, fun hpq => ?_⟩
  · rw [Matrix.mul_apply]
    exact Valuation.map_sum_le _ fun r _ => val_mul_le_one (hx p r).1 (hy r q).1
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun r _ => ?_
    by_cases hr : p.2 < r.2
    · exact val_mul_lt_one_left ((hx p r).2 hr) (hy r q).1
    · exact val_mul_lt_one_right (hx p r).1 ((hy r q).2 (lt_of_le_of_lt (not_lt.mp hr) hpq))

theorem InOrd.mul_inRad {x y : Matrix (Ix e f) (Ix e f) F} (hx : InOrd x) (hy : InRad y) :
    InRad (x * y) := by
  intro p q
  refine ⟨?_, fun hpq => ?_⟩
  · rw [Matrix.mul_apply]
    exact Valuation.map_sum_le _ fun r _ => val_mul_le_one (hx p r).1 (hy r q).1
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun r _ => ?_
    by_cases hr : p.2 < r.2
    · exact val_mul_lt_one_left ((hx p r).2 hr) (hy r q).1
    · exact val_mul_lt_one_right (hx p r).1 ((hy r q).2 (le_trans (not_lt.mp hr) hpq))

theorem InRad.mul_inOrd {x y : Matrix (Ix e f) (Ix e f) F} (hx : InRad x) (hy : InOrd y) :
    InRad (x * y) := by
  intro p q
  refine ⟨?_, fun hpq => ?_⟩
  · rw [Matrix.mul_apply]
    exact Valuation.map_sum_le _ fun r _ => val_mul_le_one (hx p r).1 (hy r q).1
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun r _ => ?_
    by_cases hr : p.2 ≤ r.2
    · exact val_mul_lt_one_left ((hx p r).2 hr) (hy r q).1
    · exact val_mul_lt_one_right (hx p r).1 ((hy r q).2 (lt_of_lt_of_le (not_le.mp hr) hpq))

/-- `U(𝔄)` for the standard principal order. -/
def J0 (F : Type uF) [Field F] [ValuativeRel F] (e f : ℕ) :
    Subgroup (GL (Ix e f) F) where
  carrier := {g | InOrd (g : Matrix (Ix e f) (Ix e f) F) ∧
    InOrd ((g⁻¹ : GL (Ix e f) F) : Matrix (Ix e f) (Ix e f) F)}
  one_mem' := ⟨by simpa using inOrd_one, by simpa using inOrd_one⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by simpa using ha.mul hb, by simpa [_root_.mul_inv_rev] using hb'.mul ha'⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by simpa using ha⟩

/-- `U^1(𝔄)` for the standard principal order. -/
def J1 (F : Type uF) [Field F] [ValuativeRel F] (e f : ℕ) :
    Subgroup (GL (Ix e f) F) where
  carrier := {g | g ∈ J0 F e f ∧ InRad ((g : Matrix (Ix e f) (Ix e f) F) - 1)}
  one_mem' := ⟨(J0 F e f).one_mem, by simpa using inRad_zero⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨(J0 F e f).mul_mem ha hb, ?_⟩
    have h : ((a * b : GL (Ix e f) F) : Matrix (Ix e f) (Ix e f) F) - 1 =
        (a : Matrix (Ix e f) (Ix e f) F) * ((b : Matrix (Ix e f) (Ix e f) F) - 1) +
          ((a : Matrix (Ix e f) (Ix e f) F) - 1) := by
      simp only [Units.val_mul]
      noncomm_ring
    rw [h]
    exact (ha.1.mul_inRad hb1).add ha1
  inv_mem' := by
    rintro a ⟨ha, ha1⟩
    refine ⟨(J0 F e f).inv_mem ha, ?_⟩
    have h : ((a⁻¹ : GL (Ix e f) F) : Matrix (Ix e f) (Ix e f) F) - 1 =
        -(((a⁻¹ : GL (Ix e f) F) : Matrix (Ix e f) (Ix e f) F) *
          ((a : Matrix (Ix e f) (Ix e f) F) - 1)) := by
      rw [mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      noncomm_ring
    rw [h]
    exact (ha.2.mul_inRad ha1).neg

theorem J1_le_J0 : J1 F e f ≤ J0 F e f := fun _ h => h.1

theorem mem_J0_of_inOrd {g : GL (Ix e f) F} (h : InOrd (g : Matrix (Ix e f) (Ix e f) F))
    (h' : InOrd ((g⁻¹ : GL (Ix e f) F) : Matrix (Ix e f) (Ix e f) F)) : g ∈ J0 F e f :=
  ⟨h, h'⟩

theorem inOrd_of_inRad_sub_one {x : Matrix (Ix e f) (Ix e f) F} (h : InRad (x - 1)) : InOrd x := by
  simpa using h.inOrd.add inOrd_one

theorem mem_J1_of_inRad {g : GL (Ix e f) F} (h : InRad ((g : Matrix (Ix e f) (Ix e f) F) - 1))
    (h' : InRad (((g⁻¹ : GL (Ix e f) F) : Matrix (Ix e f) (Ix e f) F) - 1)) : g ∈ J1 F e f :=
  ⟨⟨inOrd_of_inRad_sub_one h, inOrd_of_inRad_sub_one h'⟩, h⟩

/-- `U^1(𝔄)` is normal in `U(𝔄)`. -/
theorem conj_mem_J1 {g x : GL (Ix e f) F} (hg : g ∈ J0 F e f) (hx : x ∈ J1 F e f) :
    g * x * g⁻¹ ∈ J1 F e f := by
  refine ⟨(J0 F e f).mul_mem ((J0 F e f).mul_mem hg hx.1) ((J0 F e f).inv_mem hg), ?_⟩
  have h : ((g * x * g⁻¹ : GL (Ix e f) F) : Matrix (Ix e f) (Ix e f) F) - 1 =
      (g : Matrix (Ix e f) (Ix e f) F) * ((x : Matrix (Ix e f) (Ix e f) F) - 1) *
        ((g⁻¹ : GL (Ix e f) F) : Matrix (Ix e f) (Ix e f) F) := by
    have hGG : (g : Matrix (Ix e f) (Ix e f) F) * ((g⁻¹ : GL (Ix e f) F) :
        Matrix (Ix e f) (Ix e f) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, hGG]
  rw [h]
  exact (hg.1.mul_inRad hx.2).mul_inOrd hg.2

end Langlands.BushnellKutzko.LevelZero
