import Langlands.Global.Arithmetic.HenniartCommonBaseRealizationProof
import Langlands.Global.Arithmetic.HarrisDatumCharacterRealizationProof

/-! # Henniart's Harris datum from the weight-one CM characters -/

noncomputable section

universe uF

namespace Langlands.Global

open HarrisDatum

/-- The common-base realization and the character realization give Henniart's Harris datum,
once conjugate-inverse weight-one characters exist on CM fields. -/
theorem henniartHarrisDatum_of_halfWeight (hHalf : CMHalfWeightCharacterStatement.{0}) :
    HenniartHarrisDatumStatement.{uF} := by
  intro p hp F M
  obtain ⟨E, i₁, i₂, i₃, v₀, ι₀, hc₁, hc₂, hconf⟩ := henniartCommonBaseRealization p F M
  refine ⟨E, i₁, i₂, i₃, v₀, ι₀, hc₁, hc₂, fun F' hF' e he χ₀ => ?_⟩
  obtain ⟨E', L, j₁, j₂, j₃, j₄, j₅, j₆, j₇, j₈, j₉, K₀, P, Ps, φ, φs, θ, hconf', hv, hiso⟩ :=
    hconf F' hF'
  obtain ⟨χ, χs, ξ, hdatum, hagree⟩ :=
    harrisDatumCharacterRealization_of_halfWeight.{uF, 0, 0, 0} hHalf F F' E E' L K₀ P Ps φ φs θ
      hconf' e he χ₀
  exact ⟨E', L, j₁, j₂, j₃, j₄, j₅, j₆, j₇, j₈, j₉, K₀, P, Ps, φ, φs, θ, χ, χs, ξ, hconf', hv,
    hiso, hdatum, hagree⟩

/-- The exact target `HenniartHarrisDatumOfHalfWeightStatement`. -/
theorem henniartHarrisDatumOfHalfWeight : HenniartHarrisDatumOfHalfWeightStatement.{uF} :=
  henniartHarrisDatum_of_halfWeight

end Langlands.Global
