import Langlands.LocalField.Normalization.Continuity
import Langlands.HarmonicAnalysis.CharacterTransport

/-! # The normalized absolute value as a complex quasicharacter -/

noncomputable section

universe u

namespace Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- The actual residue-normalized absolute value, valued in complex units. -/
def normalizedAbsCharacter :
    letI := T.topology
    F.Carrierˣ →ₜ* ℂˣ := by
  let := T.topology
  refine
    { toFun := fun a => Units.mk0 (T.normalizedAbs (a : F.Carrier) : ℂ)
        (by exact_mod_cast (ne_of_gt (T.normalizedAbs_pos a.ne_zero)))
      map_one' := ?_
      map_mul' := ?_
      continuous_toFun := ?_ }
  · apply Units.ext
    simp [T.normalizedAbs_one]
  · intro a b
    apply Units.ext
    simp only [Units.val_mk0, Units.val_mul, T.normalizedAbs_mul, Complex.ofReal_mul]
  · apply Units.isEmbedding_val₀.isInducing.continuous_iff.mpr
    exact Complex.continuous_ofReal.comp
      (T.continuous_normalizedAbs.comp Units.continuous_val)

@[simp]
theorem normalizedAbsCharacter_apply (a : F.Carrierˣ) :
    (T.normalizedAbsCharacter a : ℂ) =
      (T.normalizedAbs (a : F.Carrier) : ℂ) := rfl

end Langlands.PadicField.TopologicalData
