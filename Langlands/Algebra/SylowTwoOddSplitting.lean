import Langlands.Algebra.FixedFieldScalarDefect
import Langlands.Algebra.DivisionSplittingDegree
import Mathlib.GroupTheory.Sylow

/-! # Odd-degree splitting from a cube scalar coboundary -/

noncomputable section
universe u
open Matrix
open scoped TensorProduct

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CentralSimple

variable {k L A : Type u} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- The fixed field of an actual Sylow two-subgroup of a finite Galois group
has odd degree over the ground field. -/
theorem sylowTwo_fixedField_odd_degree (P : Sylow 2 (L ≃ₐ[k] L)) :
    Odd (Module.finrank k (IntermediateField.fixedField (P : Subgroup (L ≃ₐ[k] L)))) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index,
    IntermediateField.fixingSubgroup_fixedField]
  exact Nat.not_even_iff_odd.mp (fun h => P.not_dvd_index (even_iff_two_dvd.mp h))

/-- A cube coboundary of an actual chart's scalar defect constructs an actual
splitting of the algebra over an odd-degree intermediate field. -/
theorem exists_odd_degree_splitting_of_scalarDefect_cube {n : ℕ} [NeZero n]
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (hcube : Langlands.ScalarTwoCocycle.IsCoboundary
      (fun σ τ => (splittingChartAction e).scalarDefect σ τ ^ 3)) :
    ∃ F : IntermediateField k L, Odd (Module.finrank k F) ∧
      Nonempty (F ⊗[k] A ≃ₐ[F] Matrix (Fin n) (Fin n) F) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 (L ≃ₐ[k] L) := default
  have hcop : Nat.Coprime 3 (Nat.card (P : Subgroup (L ≃ₐ[k] L))) := by
    rw [P.card_eq_multiplicity]
    exact (show Nat.Coprime 3 2 by decide).pow_right _
  exact ⟨IntermediateField.fixedField (P : Subgroup (L ≃ₐ[k] L)),
    sylowTwo_fixedField_odd_degree P,
    split_over_fixedField_of_coprime_scalarDefect_power e P 3 hcop hcube⟩

end Langlands.CentralSimple

namespace Langlands.CentralSimple

variable {k D L : Type u} [Field k] [DivisionRing D] [Algebra k D]
  [FiniteDimensional k D] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]

/-- An actual chart of a degree-six division algebra cannot have a cube
coboundary as its scalar defect. -/
theorem division_degree_six_scalarDefect_cube_not_coboundary {n : ℕ} [NeZero n]
    (hdim : Module.finrank k D = 36)
    (e : L ⊗[k] D ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    ¬ Langlands.ScalarTwoCocycle.IsCoboundary
      (fun σ τ => (splittingChartAction e).scalarDefect σ τ ^ 3) := by
  intro hcube
  obtain ⟨F, hodd, hsplit⟩ := exists_odd_degree_splitting_of_scalarDefect_cube e hcube
  exact division_degree_six_not_split_over_odd_extension hdim hodd n (NeZero.pos n) hsplit

end Langlands.CentralSimple
