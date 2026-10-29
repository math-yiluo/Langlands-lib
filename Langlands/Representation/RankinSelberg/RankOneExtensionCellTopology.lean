import Langlands.Representation.RankinSelberg.RankOneExtensionCellAlgebra

/-! # Inversion and continuity of the rank-one upper cell -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear

universe uF

variable {R : Type uF} [Field R] (t : ℕ)

theorem rankOneExtensionUpperCell_inv (y : Fin (t + 1) → R) :
    (rankOneExtensionUpperCell t y)⁻¹ = rankOneExtensionUpperCell t (-y) := by
  apply Units.ext
  rfl

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_rankOneExtensionUpperCell :
    Continuous (rankOneExtensionUpperCell (K := R) t) := by
  have hval : Continuous fun y : Fin (t + 1) → R =>
      ((rankOneExtensionUpperCell t y : Langlands.GeneralLinear (1 + (t + 1)) R) :
        Matrix (Fin (1 + (t + 1))) (Fin (1 + (t + 1))) R) := by
    apply continuous_pi
    intro r
    apply continuous_pi
    intro s
    obtain ⟨i, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective r
    obtain ⟨j, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective s
    simp only [rankOneExtensionUpperCell_apply]
    rcases i with a | a <;> rcases j with b | b <;> simp <;> fun_prop
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [rankOneExtensionUpperCell_inv]
  exact hval.comp continuous_neg

end Langlands.RankinSelberg
