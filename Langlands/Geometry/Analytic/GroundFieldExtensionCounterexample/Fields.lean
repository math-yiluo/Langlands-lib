import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Trivially normed fields with two and four elements -/

noncomputable section

namespace Langlands.Analytic.GroundFieldExtensionCounterexample

/-- The trivial absolute value on the field with two elements. -/
def trivialAbs₂ : AbsoluteValue (ZMod 2) ℝ := AbsoluteValue.trivial

open scoped Classical in
/-- The trivial absolute value on the field with four elements. -/
def trivialAbs₄ : AbsoluteValue (GaloisField 2 2) ℝ := AbsoluteValue.trivial

/-- The field with two elements and its trivial norm. -/
abbrev F₂ := WithAbs trivialAbs₂

/-- The field with four elements and its trivial norm. -/
abbrev F₄ := WithAbs trivialAbs₄

instance : Fintype F₂ := Fintype.ofEquiv (ZMod 2) (WithAbs.equiv trivialAbs₂).symm.toEquiv

instance : Finite F₄ := Finite.of_equiv (GaloisField 2 2) (WithAbs.equiv trivialAbs₄).symm.toEquiv

instance : Fintype F₄ := Fintype.ofFinite F₄

theorem norm_F₂_of_ne_zero {c : F₂} (hc : c ≠ 0) : ‖c‖ = 1 := by
  rw [WithAbs.norm_eq_apply_ofAbs]
  apply AbsoluteValue.trivial_apply
  intro h
  apply hc
  apply (WithAbs.equiv trivialAbs₂).injective
  rw [WithAbs.equiv_apply, h, map_zero]

theorem norm_F₄_of_ne_zero {c : F₄} (hc : c ≠ 0) : ‖c‖ = 1 := by
  rw [WithAbs.norm_eq_apply_ofAbs]
  classical
  unfold trivialAbs₄
  convert AbsoluteValue.trivial_apply (S := ℝ) (x := c.ofAbs) _
  intro h
  apply hc
  apply (WithAbs.equiv trivialAbs₄).injective
  rw [WithAbs.equiv_apply, h, map_zero]

theorem norm_F₂_le_one (c : F₂) : ‖c‖ ≤ 1 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (norm_F₂_of_ne_zero hc).le

theorem norm_F₄_le_one (c : F₄) : ‖c‖ ≤ 1 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (norm_F₄_of_ne_zero hc).le

instance : IsUltrametricDist F₂ :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
    rcases eq_or_ne (x + y) 0 with h | h
    · rw [h, norm_zero]
      exact le_max_of_le_left (norm_nonneg x)
    · rw [norm_F₂_of_ne_zero h]
      rcases eq_or_ne x 0 with hx | hx
      · subst hx
        rw [zero_add] at h
        exact le_max_of_le_right (norm_F₂_of_ne_zero h).ge
      · exact le_max_of_le_left (norm_F₂_of_ne_zero hx).ge

instance : IsUltrametricDist F₄ :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
    rcases eq_or_ne (x + y) 0 with h | h
    · rw [h, norm_zero]
      exact le_max_of_le_left (norm_nonneg x)
    · rw [norm_F₄_of_ne_zero h]
      rcases eq_or_ne x 0 with hx | hx
      · subst hx
        rw [zero_add] at h
        exact le_max_of_le_right (norm_F₄_of_ne_zero h).ge
      · exact le_max_of_le_left (norm_F₄_of_ne_zero hx).ge

instance : NormedAlgebra F₂ F₄ :=
  { (inferInstance : Algebra F₂ F₄) with
    norm_smul_le := fun c x => by
      rcases eq_or_ne c 0 with rfl | hc
      · simp
      · rw [Algebra.smul_def, norm_mul, norm_F₂_of_ne_zero hc, one_mul]
        exact mul_le_of_le_one_left (norm_nonneg x) (norm_F₄_le_one _) }

end Langlands.Analytic.GroundFieldExtensionCounterexample
