import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! # Scalar ambiguity of conjugation on special linear groups -/

noncomputable section

universe u v

namespace Langlands.LinearAlgebra.SpecialLinearConjugation

open Matrix

variable {I : Type u} {R : Type v} [Fintype I] [DecidableEq I] [CommRing R]

/-- Conjugation by an invertible matrix, restricted to determinant-one matrices. -/
def conjugation (X : GeneralLinearGroup I R) :
    SpecialLinearGroup I R →* GeneralLinearGroup I R where
  toFun g := X * SpecialLinearGroup.toGL g * X⁻¹
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul]
    group

/-- A matrix commuting with every determinant-one matrix is scalar. -/
theorem mem_range_scalar_of_commute (X : Matrix I I R)
    (h : ∀ g : SpecialLinearGroup I R, Commute (g : Matrix I I R) X) :
    X ∈ Set.range (Matrix.scalar I) := by
  apply Matrix.mem_range_scalar_of_commute_transvectionStruct
  intro t
  exact h t.toSpecialLinearGroup

/-- An invertible matrix centralizing the special linear group is a unit scalar. -/
theorem exists_unit_scalar_of_commute (X : GeneralLinearGroup I R)
    (h : ∀ g : SpecialLinearGroup I R,
      X * SpecialLinearGroup.toGL g = SpecialLinearGroup.toGL g * X) :
    ∃ c : Rˣ, GeneralLinearGroup.scalar I c = X := by
  have hscalar : (X : Matrix I I R) ∈ Set.range (Matrix.scalar I) := by
    apply mem_range_scalar_of_commute
    intro g
    exact (congrArg (fun z : GeneralLinearGroup I R => (z : Matrix I I R)) (h g)).symm
  have hc : X ∈ Subgroup.center (GeneralLinearGroup I R) :=
    GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr hscalar
  rwa [GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] at hc

/-- A conjugation acting identically on the special linear group is scalar. -/
theorem exists_unit_scalar_of_conjugation_eq (X : GeneralLinearGroup I R)
    (h : ∀ g : SpecialLinearGroup I R,
      X * SpecialLinearGroup.toGL g * X⁻¹ = SpecialLinearGroup.toGL g) :
    ∃ c : Rˣ, GeneralLinearGroup.scalar I c = X := by
  apply exists_unit_scalar_of_commute X
  intro g
  exact (mul_inv_eq_iff_eq_mul).mp (h g)

/-- Two conjugating matrices with the same action on `SL` differ by a unit scalar. -/
theorem exists_unit_scalar_of_conjugation_eq_conjugation
    (X Y : GeneralLinearGroup I R)
    (h : ∀ g : SpecialLinearGroup I R,
      X * SpecialLinearGroup.toGL g * X⁻¹ =
        Y * SpecialLinearGroup.toGL g * Y⁻¹) :
    ∃ c : Rˣ, X = Y * GeneralLinearGroup.scalar I c := by
  obtain ⟨c, hc⟩ := exists_unit_scalar_of_conjugation_eq (Y⁻¹ * X) (by
    intro g
    calc
      (Y⁻¹ * X) * SpecialLinearGroup.toGL g * (Y⁻¹ * X)⁻¹ =
          Y⁻¹ * (X * SpecialLinearGroup.toGL g * X⁻¹) * Y := by group
      _ = Y⁻¹ * (Y * SpecialLinearGroup.toGL g * Y⁻¹) * Y := by rw [h g]
      _ = SpecialLinearGroup.toGL g := by group)
  refine ⟨c, ?_⟩
  rw [hc]
  group

/-- Normalizing one diagonal entry to one removes the scalar ambiguity. -/
theorem eq_of_conjugation_eq_of_entry_eq_one (X Y : GeneralLinearGroup I R) (p : I)
    (hX : (X : Matrix I I R) p p = 1) (hY : (Y : Matrix I I R) p p = 1)
    (h : ∀ g : SpecialLinearGroup I R,
      X * SpecialLinearGroup.toGL g * X⁻¹ =
        Y * SpecialLinearGroup.toGL g * Y⁻¹) :
    X = Y := by
  obtain ⟨c, hc⟩ := exists_unit_scalar_of_conjugation_eq_conjugation X Y h
  have he := congrArg (fun z : GeneralLinearGroup I R => (z : Matrix I I R) p p) hc
  have hc1 : (c : R) = 1 := by
    simpa [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.mul_diagonal, hX, hY] using he.symm
  have hcunit : c = 1 := Units.ext hc1
  simpa [hcunit] using hc

end Langlands.LinearAlgebra.SpecialLinearConjugation
