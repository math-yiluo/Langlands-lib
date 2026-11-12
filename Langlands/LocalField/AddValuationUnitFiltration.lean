import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Basic.NNReal.Defs
import Mathlib.Tactic.Ring

/-! # Real-depth congruence subgroups of valued field units -/

noncomputable section

universe u v

open scoped NNReal

namespace Langlands.LocalField

variable {K : Type u} [Field K] (ω : AddValuation K (WithTop ℝ))

/-- Units of valuation zero congruent to one to nonnegative real depth `r`. -/
def addValuationUnitFiltration (r : ℝ≥0) : Subgroup Kˣ where
  carrier := {x | ω (x : K) = 0 ∧ ((r : ℝ) : WithTop ℝ) ≤ ω ((x : K) - 1)}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    refine ⟨by simp only [Units.val_mul, ω.map_mul, hx.1, hy.1, add_zero], ?_⟩
    change ((r : ℝ) : WithTop ℝ) ≤ ω ((x : K) * (y : K) - 1)
    rw [show (x : K) * (y : K) - 1 = ((x : K) - 1) * (y : K) + ((y : K) - 1) by ring]
    apply ω.map_le_add
    · simpa only [ω.map_mul, hy.1, add_zero] using hx.2
    · exact hy.2
  inv_mem' := by
    intro x hx
    have hinv : ω ((x⁻¹ : Kˣ) : K) = 0 := by
      simp only [Units.val_inv_eq_inv_val, ω.map_inv, hx.1, neg_zero]
    refine ⟨hinv, ?_⟩
    rw [show ((x⁻¹ : Kˣ) : K) - 1 = -((x : K) - 1) * ((x⁻¹ : Kˣ) : K) by
      rw [neg_mul, sub_mul, Units.mul_inv, one_mul]
      ring]
    simpa only [ω.map_mul, ω.map_neg, hinv, add_zero] using hx.2

@[simp] theorem mem_addValuationUnitFiltration (r : ℝ≥0) (x : Kˣ) :
    x ∈ addValuationUnitFiltration ω r ↔
      ω (x : K) = 0 ∧ ((r : ℝ) : WithTop ℝ) ≤ ω ((x : K) - 1) := Iff.rfl

/-- At positive depth, congruence to one already forces valuation zero. -/
theorem mem_addValuationUnitFiltration_of_pos {r : ℝ≥0} (hr : 0 < r) (x : Kˣ) :
    x ∈ addValuationUnitFiltration ω r ↔
      ((r : ℝ) : WithTop ℝ) ≤ ω ((x : K) - 1) := by
  refine ⟨fun h => h.2, fun hx => ⟨?_, hx⟩⟩
  have hpos : (0 : WithTop ℝ) < ω ((x : K) - 1) :=
    lt_of_lt_of_le (by exact_mod_cast hr) hx
  simpa only [ω.map_one] using
    ω.map_eq_of_lt_sub (x := 1) (y := (x : K)) (by simpa using hpos)

/-- Level zero is exactly the group of units of valuation zero. -/
theorem mem_addValuationUnitFiltration_zero (x : Kˣ) :
    x ∈ addValuationUnitFiltration ω 0 ↔ ω (x : K) = 0 := by
  refine ⟨fun h => h.1, fun hx => ⟨hx, ?_⟩⟩
  simpa only [NNReal.coe_zero, WithTop.coe_zero, hx, ω.map_one, min_self] using
    ω.map_sub (x : K) 1

/-- Higher congruence depth gives a smaller subgroup. -/
theorem addValuationUnitFiltration_antitone : Antitone (addValuationUnitFiltration ω) := by
  intro r s hrs x hx
  exact ⟨hx.1, le_trans (by exact_mod_cast hrs) hx.2⟩

/-- A unit congruent to one to every depth is one. -/
theorem eq_one_of_mem_addValuationUnitFiltration (x : Kˣ)
    (hx : ∀ r : ℝ≥0, x ∈ addValuationUnitFiltration ω r) : x = 1 := by
  apply Units.ext
  apply sub_eq_zero.mp
  apply ω.top_iff.mp
  apply WithTop.eq_top_iff_forall_ge.mpr
  intro b
  have hb : b ≤ (⟨max b 0, le_max_right b 0⟩ : ℝ≥0) := le_max_left b 0
  exact (by exact_mod_cast hb : (b : WithTop ℝ) ≤ ↑((⟨max b 0, le_max_right b 0⟩ :
    ℝ≥0) : ℝ)).trans (hx _).2

/-- The congruence filtration is separated. -/
theorem iInf_addValuationUnitFiltration_eq_bot :
    ⨅ r : ℝ≥0, addValuationUnitFiltration ω r = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  exact (Subgroup.mem_bot).mpr
    (eq_one_of_mem_addValuationUnitFiltration ω x (Subgroup.mem_iInf.mp hx))

variable {L : Type v} [Field L] (ν : AddValuation L (WithTop ℝ))

/-- A ring map preserving the valuation preserves every unit congruence subgroup. -/
theorem map_addValuationUnitFiltration_le (f : K →+* L)
    (hf : ∀ x : K, ν (f x) = ω x) (r : ℝ≥0) :
    (addValuationUnitFiltration ω r).map (Units.map f.toMonoidHom) ≤
      addValuationUnitFiltration ν r := by
  rintro _ ⟨x, hx, rfl⟩
  change ν (f (x : K)) = 0 ∧
    ((r : ℝ) : WithTop ℝ) ≤ ν (f (x : K) - 1)
  rw [← f.map_one, ← f.map_sub, hf, hf]
  exact hx

end Langlands.LocalField
