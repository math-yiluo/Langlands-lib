import Langlands.Algebra.DivisionFieldEmbeddingsProof
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic.Group

/-! The unit twist used to move an original element into a field image. -/

noncomputable section

namespace Langlands.CentralDivision

universe uK uD uL

open scoped commutatorElement

variable {K : Type uK} [Field K] {D : Type uD} [DivisionRing D] [Algebra K D]
  {L : Type uL} [Field L] [Algebra K L]

/-- The original unit corrected by two units from an actual embedded field. -/
def fieldMovementTwist (ι : L →ₐ[K] D) (a : Dˣ) (a' b : Lˣ) : Dˣ :=
  a * (Units.map ι.toMonoidHom a')⁻¹ * Units.map ι.toMonoidHom b

/-- Conjugating the corrected unit into the field moves the original unit modulo a commutator. -/
theorem move_unit_of_conjugate_fieldMovementTwist (ι : L →ₐ[K] D)
    (a : Dˣ) (a' b y : Lˣ) (u : Dˣ)
    (hconj : fieldMovementTwist ι a a' b = u * Units.map ι.toMonoidHom y * u⁻¹) :
    ∃ c ∈ commutator Dˣ, c * a ∈ (Units.map ι.toMonoidHom).range := by
  let t := fieldMovementTwist ι a a' b
  refine ⟨⁅u⁻¹, t⁆, Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
  refine ⟨y * b⁻¹ * a', ?_⟩
  simp only [map_mul, map_inv]
  change _ = ⁅u⁻¹, fieldMovementTwist ι a a' b⁆ * a
  rw [hconj]
  have ha : a = (u * Units.map ι.toMonoidHom y * u⁻¹) *
      (Units.map ι.toMonoidHom b)⁻¹ * Units.map ι.toMonoidHom a' := by
    rw [← hconj, fieldMovementTwist]
    group
  rw [ha]
  group

end Langlands.CentralDivision
