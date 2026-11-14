import Langlands.Representation.Geometric.RefinedPositiveCharacter
import Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement
import Langlands.AllField.Representation.Geometric.RefinementDefinitionsSupplement
import Langlands.AllField.Representation.Parabolic.UnipotentFiniteContainment
/-! Positive characters on actual p-adic refined parabolics factor through the Levi. -/

noncomputable section

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.Geometric
open scoped NNReal

universe uF

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
  (S : BlockRefinement B)

/-- Restriction of a positive character to the actual refined Levi section. -/
def refinedPositiveLeviCharacter
    (χ : refinedParabolic F B S →* ℝ≥0ˣ) :
    refinedLevi F B S →* ℝ≥0ˣ :=
  χ.comp (refinedLeviSection F B S)

/-- A continuous positive character is trivial on the actual refined radical. -/
theorem refinedPositiveCharacter_unipotent
    (χ : refinedParabolic F B S →* ℝ≥0ˣ)
    (hχ : letI := T.topology; Continuous χ)
    (u : refinedUnipotentRadical F B S) : χ u.val = 1 := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let v : refinedUnipotent F B S :=
    ⟨u.val.val, (mem_refinedUnipotentRadical F B S u.val).mp u.property⟩
  let f : refinedUnipotent F B S →* ℝ≥0ˣ :=
    χ.comp (Subgroup.inclusion (refinedUnipotent_le_parabolic F B S))
  have hf : Continuous f := hχ.comp (continuous_subtype_val.subtype_mk _)
  obtain ⟨K, hK, hmem⟩ := T.refinedUnipotent_finite_containment B S {v}
  change f v = 1
  exact RankinSelberg.LastRowReduction.eq_one_of_isCompact f hf K.toSubgroup hK
    (hmem v (Finset.mem_singleton_self v))

/-- The full character is its actual Levi restriction inflated by the projection. -/
theorem refinedPositiveCharacter_factor
    (χ : refinedParabolic F B S →* ℝ≥0ˣ)
    (hχ : letI := T.topology; Continuous χ) (q : refinedParabolic F B S) :
    χ q = refinedPositiveLeviCharacter B S χ
      (refinedLeviProjection F B S q) := by
  have he := (refinedDecomposition F B S).symm_apply_apply q
  change (refinedUnipotentPart F B S q).val *
    refinedLeviSection F B S (refinedLeviProjection F B S q) = q at he
  calc
    χ q = χ ((refinedUnipotentPart F B S q).val *
        refinedLeviSection F B S (refinedLeviProjection F B S q)) :=
      congrArg χ he.symm
    _ = _ := by
      rw [map_mul, T.refinedPositiveCharacter_unipotent B S χ hχ, one_mul]
      rfl

end Langlands.LocalFieldData
