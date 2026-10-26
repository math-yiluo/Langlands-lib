import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeStatement
import Langlands.Representation.Twist.SmoothProof
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Group.GL.CompactOpen

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF

theorem scalar_isOfWhittakerType_rankOne
    {F : Type uF} [Field F] [TopologicalSpace F]
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear 1 F) ℂ)
    (hπ : IsSmooth π) :
    IsOfWhittakerType 0 (standardCharacter ψ 0) π := by
  refine ⟨⟨hπ, fun _ => inferInstance⟩, ?_, ?_⟩
  · exact Module.Finite.of_restrictScalars_finite ℂ _ _
  · change Nonempty ((glFunctionals ψ 0 π) ≃ₗ[ℂ] ℂ)
    rw [glFunctionals_rankOne]
    exact ⟨(Submodule.topEquiv).trans (LinearMap.ringLmapEquivSelf ℂ ℂ ℂ)⟩

theorem rankOneCharacter_isOfWhittakerType
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType 0 (standardCharacter ψ 0)
      (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalGeneralLinearNonarchimedean 1
  apply scalar_isOfWhittakerType_rankOne
  let χdet : Langlands.GeneralLinear 1 F.Carrier →* ℂˣ :=
    (χ : F.Carrierˣ →* ℂˣ).comp determinant
  have hopen : IsOpen (χdet.ker : Set (Langlands.GeneralLinear 1 F.Carrier)) :=
    isOpen_ker_of_continuous_complex_character χdet
      (χ.continuous.comp (F.canonicalTopologicalData.generalLinearDeterminant 1).continuous)
  apply (isSmooth_twist_iff χdet (Representation.trivial ℂ _ ℂ) hopen).mpr
  intro v
  refine ⟨⊤, ?_⟩
  intro g
  rfl

theorem rankOneWhittakerType : RankOneWhittakerTypeStatement.{uF} :=
  rankOneCharacter_isOfWhittakerType

end Langlands.RankinSelberg
