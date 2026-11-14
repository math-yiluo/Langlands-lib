import Langlands.Representation.RankinSelberg.RankOneExtensionCharacter
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof
noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker hiding functionalsCongr
open Langlands.GeneralLinear

universe uF uW

/-- The exact lifted scalar action used by the rank-one extension target. -/
abbrev rankOneExtensionCharacter
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (χ : Quasicharacter F) :
    Representation ℂ (Langlands.GeneralLinear 1 F) (ULift.{uW} ℂ) :=
  (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
    (rankOneCharacter (χ : Fˣ →* ℂˣ))

/-- Full Whittaker type transports to the exact lifted scalar action. -/
theorem rankOneExtensionCharacter_isOfWhittakerType
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (χ : Quasicharacter F) :
    IsOfWhittakerType 0 (standardCharacter ψ 0)
      (rankOneExtensionCharacter.{uF, uW} F χ) := by
  exact (rankOneWhittakerType F ψ χ).of_equiv
    (Representation.Equiv.mk ULift.moduleEquiv.symm (by intro g; rfl))

/-- The lifted rank-one action is smooth in the canonical topology. -/
theorem rankOneExtensionCharacter_isSmooth
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (χ : Quasicharacter F) :
    IsSmooth (rankOneExtensionCharacter.{uF, uW} F χ) :=
  (rankOneExtensionCharacter_isOfWhittakerType F ψ χ).1.1

end Langlands.AllField.RankinSelberg
