import Langlands.Representation.Parabolic.UnipotentFiniteContainment
import Langlands.Topology.CompactNormCharacter

/-! Positive characters on actual p-adic refined parabolics factor through the Levi. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open Geometric
open scoped NNReal

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
  (S : BlockRefinement B)

/-- Restriction of a positive character to the actual refined Levi section. -/
def refinedPositiveLeviCharacter
    (χ : refinedParabolic F.Carrier B S →* ℝ≥0ˣ) :
    refinedLevi F.Carrier B S →* ℝ≥0ˣ :=
  χ.comp (refinedLeviSection F.Carrier B S)

/-- A continuous positive character is trivial on the actual refined radical. -/
theorem refinedPositiveCharacter_unipotent
    (χ : refinedParabolic F.Carrier B S →* ℝ≥0ˣ)
    (hχ : letI := T.topology; Continuous χ)
    (u : refinedUnipotentRadical F.Carrier B S) : χ u.val = 1 := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let v : refinedUnipotent F.Carrier B S :=
    ⟨u.val.val, (mem_refinedUnipotentRadical F.Carrier B S u.val).mp u.property⟩
  let f : refinedUnipotent F.Carrier B S →* ℝ≥0ˣ :=
    χ.comp (Subgroup.inclusion (refinedUnipotent_le_parabolic F.Carrier B S))
  have hf : Continuous f := hχ.comp (continuous_subtype_val.subtype_mk _)
  obtain ⟨K, hK, hmem⟩ := T.refinedUnipotent_finite_containment B S {v}
  change f v = 1
  exact RankinSelberg.LastRowReduction.eq_one_of_isCompact f hf K.toSubgroup hK
    (hmem v (Finset.mem_singleton_self v))

/-- The full character is its actual Levi restriction inflated by the projection. -/
theorem refinedPositiveCharacter_factor
    (χ : refinedParabolic F.Carrier B S →* ℝ≥0ˣ)
    (hχ : letI := T.topology; Continuous χ) (q : refinedParabolic F.Carrier B S) :
    χ q = refinedPositiveLeviCharacter B S χ
      (refinedLeviProjection F.Carrier B S q) := by
  have he := (refinedDecomposition F.Carrier B S).symm_apply_apply q
  change (refinedUnipotentPart F.Carrier B S q).val *
    refinedLeviSection F.Carrier B S (refinedLeviProjection F.Carrier B S q) = q at he
  calc
    χ q = χ ((refinedUnipotentPart F.Carrier B S q).val *
        refinedLeviSection F.Carrier B S (refinedLeviProjection F.Carrier B S q)) :=
      congrArg χ he.symm
    _ = _ := by
      rw [map_mul, T.refinedPositiveCharacter_unipotent B S χ hχ, one_mul]
      rfl

end Langlands.PadicField.TopologicalData
