import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! The actual residue division ring of a valuation on a possibly noncommutative division ring. -/

noncomputable section

namespace Langlands.DivisionValuation

universe u v

variable {D : Type u} {Γ₀ : Type v} [DivisionRing D]
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation D Γ₀)

/-- An integral element is a unit in the integer subring exactly when its value is one. -/
theorem isUnit_iff_value_eq_one (x : v.integer) :
    IsUnit x ↔ v (x : D) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    apply le_antisymm u.val.prop
    have h : v (u.val : D) * v ((u⁻¹).val : D) = 1 := by
      rw [← map_mul]
      change v ((u.val * (u⁻¹).val : v.integer) : D) = 1
      simp
    calc
      1 = v (u.val : D) * v ((u⁻¹).val : D) := h.symm
      _ ≤ v (u.val : D) * 1 := mul_le_mul_of_nonneg_left (u⁻¹).val.prop zero_le
      _ = v (u.val : D) := mul_one _
  · intro hx
    have hx0 : (x : D) ≠ 0 := by
      intro h
      simp [h] at hx
    let y : v.integer := ⟨(x : D)⁻¹, by
      change v ((x : D)⁻¹) ≤ 1
      rw [v.map_inv, hx, inv_one]⟩
    exact ⟨⟨x, y, Subtype.ext (mul_inv_cancel₀ hx0),
      Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

/-- The strict-value ideal consists of the integral elements of value less than one. -/
def strictIdeal : Ideal v.integer where
  carrier := {x | v (x : D) < 1}
  zero_mem' := by simp
  add_mem' hx hy := v.map_add_lt hx hy
  smul_mem' r x hx := by
    change v ((r : D) * (x : D)) < 1
    rw [map_mul]
    exact mul_lt_of_le_one_of_lt r.prop hx

@[simp]
theorem mem_strictIdeal (x : v.integer) : x ∈ strictIdeal v ↔ v (x : D) < 1 := Iff.rfl

instance strictIdeal_isTwoSided : (strictIdeal v).IsTwoSided where
  mul_mem_of_left b ha := by
    change v ((_ : D) * (b : D)) < 1
    rw [map_mul, mul_comm]
    exact mul_lt_of_le_one_of_lt b.prop ha

/-- The strict-value ideal is exactly the set of nonunits, including in the noncommutative case. -/
theorem mem_strictIdeal_iff_not_isUnit (x : v.integer) :
    x ∈ strictIdeal v ↔ ¬ IsUnit x := by
  rw [mem_strictIdeal, isUnit_iff_value_eq_one]
  exact lt_iff_le_and_ne.trans (and_iff_right x.prop)

/-- The strict-value ideal is maximal as a left ideal, not merely as a two-sided ideal. -/
instance strictIdeal_isMaximal : (strictIdeal v).IsMaximal := by
  apply Ideal.isMaximal_iff.mpr
  refine ⟨by simp, ?_⟩
  intro J x _ hx hJ
  have hu : IsUnit x := by
    by_contra h
    exact hx ((mem_strictIdeal_iff_not_isUnit v x).mpr h)
  obtain ⟨u, rfl⟩ := hu
  simpa using J.mul_mem_left (u⁻¹ : v.integerˣ) hJ

/-- Every proper left ideal of the integer subring lies in the strict-value ideal. -/
theorem le_strictIdeal_of_ne_top (J : Ideal v.integer) (hJ : J ≠ ⊤) :
    J ≤ strictIdeal v := by
  intro x hx
  apply (mem_strictIdeal_iff_not_isUnit v x).mpr
  rintro ⟨u, rfl⟩
  apply hJ
  apply (Ideal.eq_top_iff_one J).mpr
  simpa using J.mul_mem_left (u⁻¹ : v.integerˣ) hx

/-- The actual quotient of the integer subring by its strict-value ideal. -/
abbrev Residue := v.integer ⧸ strictIdeal v

instance residueDivisionRing : DivisionRing (Residue v) :=
  Ideal.Quotient.divisionRing (strictIdeal v)

/-- Reduction from the original integer subring to its residue division ring. -/
def reduction : v.integer →+* Residue v := Ideal.Quotient.mk (strictIdeal v)

theorem reduction_surjective : Function.Surjective (reduction v) :=
  Ideal.Quotient.mk_surjective

@[simp]
theorem reduction_eq_zero_iff (x : v.integer) :
    reduction v x = 0 ↔ v (x : D) < 1 :=
  Ideal.Quotient.eq_zero_iff_mem

@[simp]
theorem reduction_ne_zero_iff (x : v.integer) :
    reduction v x ≠ 0 ↔ v (x : D) = 1 := by
  rw [ne_eq, reduction_eq_zero_iff, not_lt]
  exact ⟨fun h => le_antisymm x.prop h, fun h => h.ge⟩

theorem reduction_eq_iff (x y : v.integer) :
    reduction v x = reduction v y ↔ v ((x : D) - (y : D)) < 1 := by
  rw [← sub_eq_zero, ← map_sub, reduction_eq_zero_iff]
  rfl

/-- Every unit of the residue division ring lifts to a unit of the original integer subring. -/
theorem reduction_units_surjective :
    Function.Surjective (Units.map (reduction v).toMonoidHom) := by
  intro u
  obtain ⟨x, hx⟩ := reduction_surjective v (u : Residue v)
  have hunit : IsUnit x := (isUnit_iff_value_eq_one v x).mpr
    ((reduction_ne_zero_iff v x).mp (hx ▸ u.ne_zero))
  refine ⟨hunit.unit, ?_⟩
  apply Units.ext
  change reduction v (hunit.unit : v.integer) = (u : Residue v)
  rw [hunit.unit_spec]
  exact hx

/-- A unit reduces to one exactly when its difference from one has strict value. -/
theorem reduction_unit_eq_one_iff (u : v.integerˣ) :
    Units.map (reduction v).toMonoidHom u = 1 ↔ v ((u.val : D) - 1) < 1 := by
  rw [← Units.val_inj]
  change reduction v u.val = 1 ↔ _
  rw [← (reduction v).map_one, reduction_eq_iff]
  rfl

end Langlands.DivisionValuation
