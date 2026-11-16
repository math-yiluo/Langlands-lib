import Langlands.Global.RankinSelberg.DualExpansionRectMeasure
import Langlands.Global.RankinSelberg.DualExpansionFinal

/-! # The zero-row rectangle has mass one and equals the padded chart -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance emptyRectangleSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance emptyRectangleMeasurableSpace (F : Type u) [Field F]
    [NumberField F] (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

variable (F : Type u) [Field F] [NumberField F]

section EmptyRectangle

variable [CompactSpace (AdeleQuotient F)]

/-- The zero-row rectangular space has total covolume-one measure one. -/
theorem rectangleMeasure_zero_rows_univ (m : ℕ) :
    rectangleMeasure F 0 m Set.univ = 1 := by
  have hd : rectDomain F 0 m = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    obtain ⟨c, hc, -⟩ := existsUnique_add_mem_rectDomain F 0 m 0
    have he : (c : Matrix (Fin 0) (Fin m) (Adeles F)) + 0 = x := Subsingleton.elim _ _
    exact he ▸ hc
  rw [← hd]
  exact rectangleMeasure_rectDomain F 0 m

/-- If the rectangle has no rows, its integral is exactly evaluation on the
padded point, including the measure normalization. -/
theorem lintegral_rectangular_eq_pad_of_gap_eq_zero {r t : ℕ} (h : t < r)
    (hgap : r - (t + 1) = 0) (g : Points F (t + 1))
    (Ξ : Points F (r + 1) → ℝ≥0∞) :
    (∫⁻ x, Ξ (rectangularPoint F h g x)
      ∂rectangleMeasure F (r - (t + 1)) (t + 1)) =
      Ξ (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g) := by
  have hz : ∀ x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F), x = 0 := by
    intro x
    funext i
    have hi := i.isLt
    omega
  have he : (fun x => Ξ (rectangularPoint F h g x)) =
      fun _ : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F) =>
        Ξ (rectangularPoint F h g 0) := by
    funext x
    rw [hz x]
  rw [he, lintegral_const, ← pad_eq_rectangularPoint]
  have hm : rectangleMeasure F (r - (t + 1)) (t + 1) Set.univ = 1 := by
    rw [hgap]
    exact rectangleMeasure_zero_rows_univ F (t + 1)
  rw [hm, mul_one]

end EmptyRectangle

end Langlands.Global.RankinSelbergGlobal
