import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.AllField.LocalField.Foundation
/-!
# Proof of the real norm decomposition of a smooth scalar character

A character of `F^×` with open kernel has absolute value one on the norm-one
units, because these units form a compact group in which the kernel is an open
subgroup of finite index. Every unit is a norm-one unit times an integer power of
the specified uniformizer, so the absolute value of the character is
`‖ω ϖ‖ ^ ord a`, which is `|a| ^ c` for `c = -log_q ‖ω ϖ‖`. The exponent is
unique because `0 < |ϖ| = q⁻¹ < 1`.
-/

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF


open Langlands.LocalFactor.PadicAbelian hiding uniformizerUnit uniformizerUnit_coe uniformizerUnit_ord uniformizerUnit_zpow_abs uniformizerUnit_zpow_value
open Langlands.LocalFactor.LocalAbelian (uniformizerUnit uniformizerUnit_coe uniformizerUnit_ord uniformizerUnit_zpow_abs uniformizerUnit_zpow_value)

section Helpers

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The residue-normalized absolute value is one exactly on the valuation-one locus. -/
theorem normalizedAbs_eq_one_iff_valuation_eq_one (x : F) :
    T.normalizedAbs x = 1 ↔
      (letI := T.valuativeRel; ValuativeRel.valuation F x = 1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  by_cases hx : x = 0
  · simp [hx, T.normalizedAbs_zero]
  have h := T.normalizedAbs_le_iff_of_ne_zero hx (one_ne_zero : (1 : F) ≠ 0)
  have h' := T.normalizedAbs_le_iff_of_ne_zero (one_ne_zero : (1 : F) ≠ 0) hx
  rw [T.normalizedAbs_one, map_one] at h h'
  rw [le_antisymm_iff, h, h', ← le_antisymm_iff]
  change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)
      (ValuativeRel.valuation F x) = 1 ↔ _
  rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)]
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).injective.eq_iff

/-- The units of residue-normalized absolute value one are compact in the
topology of units induced by the supplied field topology. -/
theorem isCompact_normalizedAbs_eq_one_units :
    letI := T.topology
    IsCompact {a : Fˣ | T.normalizedAbs (a : F) = 1} := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let S : Set F := {x | ValuativeRel.valuation F x = 1}
  have hS : IsCompact S := by
    have hcl : IsClosed S := by
      simpa only [Valuation.restrict_eq_one_iff] using
        (ValuativeRel.valuation F).isClosed_sphere (r := 1)
    exact (IsNonarchimedeanLocalField.isCompact_closedBall F 1).of_isClosed_subset hcl
      fun x hx => le_of_eq hx
  have he : {a : Fˣ | T.normalizedAbs (a : F) = 1} = Units.val ⁻¹' S := by
    ext a
    exact T.normalizedAbs_eq_one_iff_valuation_eq_one a
  rw [he]
  refine Units.isEmbedding_val₀.isInducing.isCompact_preimage' hS fun x hx => ?_
  have hx0 : x ≠ 0 := by
    rintro rfl
    have hx' : ValuativeRel.valuation F (0 : F) = 1 := hx
    rw [map_zero] at hx'
    exact zero_ne_one hx'
  exact ⟨Units.mk0 x hx0, rfl⟩

end Helpers

end Langlands.LocalFieldData
