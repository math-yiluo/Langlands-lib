import Mathlib.NumberTheory.LocalField.Basic

/-! # Residues of integral elements of a nonarchimedean local field -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The residue of an integral element, extended by zero to nonintegral elements. -/
def res (x : F) : 𝓀[F] :=
  if h : valuation F x ≤ 1 then IsLocalRing.residue 𝒪[F] ⟨x, h⟩ else 0

theorem res_of_le {x : F} (h : valuation F x ≤ 1) : res x = IsLocalRing.residue 𝒪[F] ⟨x, h⟩ := by
  simp [res, h]

theorem res_add {x y : F} (hx : valuation F x ≤ 1) (hy : valuation F y ≤ 1) :
    res (x + y) = res x + res y := by
  have hxy : valuation F (x + y) ≤ 1 := Valuation.map_add_le _ hx hy
  rw [res_of_le hxy, res_of_le hx, res_of_le hy, ← map_add]
  rfl

theorem res_mul {x y : F} (hx : valuation F x ≤ 1) (hy : valuation F y ≤ 1) :
    res (x * y) = res x * res y := by
  have hxy : valuation F (x * y) ≤ 1 := by rw [map_mul]; exact mul_le_one' hx hy
  rw [res_of_le hxy, res_of_le hx, res_of_le hy, ← map_mul]
  rfl

theorem res_neg {x : F} (hx : valuation F x ≤ 1) : res (-x) = -res x := by
  have hx' : valuation F (-x) ≤ 1 := by rwa [Valuation.map_neg]
  rw [res_of_le hx', res_of_le hx, ← map_neg]
  rfl

theorem res_sub {x y : F} (hx : valuation F x ≤ 1) (hy : valuation F y ≤ 1) :
    res (x - y) = res x - res y := by
  have hy' : valuation F (-y) ≤ 1 := by rwa [Valuation.map_neg]
  rw [sub_eq_add_neg, res_add hx hy', res_neg hy, sub_eq_add_neg]

@[simp] theorem res_zero : res (0 : F) = 0 := by
  rw [res_of_le (by simp)]
  exact map_zero _

@[simp] theorem res_one : res (1 : F) = 1 := by
  rw [res_of_le (by simp)]
  exact map_one _

theorem res_eq_zero_iff {x : F} (hx : valuation F x ≤ 1) : res x = 0 ↔ valuation F x < 1 := by
  rw [res_of_le hx, IsLocalRing.residue_eq_zero_iff]
  exact ⟨fun h => (valuation F).mem_maximalIdeal_iff.mp h,
    fun h => (valuation F).mem_maximalIdeal_iff.mpr h⟩

theorem res_eq_res_iff {x y : F} (hx : valuation F x ≤ 1) (hy : valuation F y ≤ 1) :
    res x = res y ↔ valuation F (x - y) < 1 := by
  rw [← sub_eq_zero, ← res_sub hx hy, res_eq_zero_iff (Valuation.map_sub_le _ hx hy)]

theorem res_sum {ι : Type*} (s : Finset ι) (g : ι → F) (hg : ∀ i ∈ s, valuation F (g i) ≤ 1) :
    res (∑ i ∈ s, g i) = ∑ i ∈ s, res (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      res_add (hg a (Finset.mem_insert_self a s))
        (Valuation.map_sum_le _ fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

/-- An integral lift of a residue class. -/
def lift (c : 𝓀[F]) : F := ((IsLocalRing.residue_surjective c).choose : 𝒪[F])

theorem lift_le_one (c : 𝓀[F]) : valuation F (lift c) ≤ 1 :=
  ((IsLocalRing.residue_surjective c).choose).property

@[simp] theorem res_lift (c : 𝓀[F]) : res (lift c) = c := by
  rw [res_of_le (lift_le_one c)]
  exact (IsLocalRing.residue_surjective c).choose_spec

theorem val_lt_one_of_res_eq_zero {x : F} (hx : valuation F x ≤ 1) (h : res x = 0) :
    valuation F x < 1 := (res_eq_zero_iff hx).mp h

end Langlands.BushnellKutzko.LevelZero
