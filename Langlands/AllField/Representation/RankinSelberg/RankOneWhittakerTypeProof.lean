import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeStatement
noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF

theorem rankOneCharacter_isOfWhittakerType
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (χ : Quasicharacter F) :
    IsOfWhittakerType 0 (standardCharacter ψ 0)
      (rankOneCharacter (χ : Fˣ →* ℂˣ)) := by
  let := (⟨⟩ : LocalFieldData F).generalLinearNonarchimedean 1
  apply scalar_isOfWhittakerType_rankOne
  let χdet : Langlands.GeneralLinear 1 F →* ℂˣ :=
    (χ : Fˣ →* ℂˣ).comp determinant
  have hopen : IsOpen (χdet.ker : Set (Langlands.GeneralLinear 1 F)) :=
    isOpen_ker_of_continuous_complex_character χdet
      (χ.continuous.comp ((⟨⟩ : LocalFieldData F).generalLinearDeterminant 1).continuous)
  apply (isSmooth_twist_iff χdet (Representation.trivial ℂ _ ℂ) hopen).mpr
  intro v
  refine ⟨⊤, ?_⟩
  intro g
  rfl

theorem rankOneWhittakerType : RankOneWhittakerTypeStatement.{uF} :=
  rankOneCharacter_isOfWhittakerType

end Langlands.AllField.RankinSelberg
