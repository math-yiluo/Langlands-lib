import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uW

/-- The exact lifted scalar action used by the rank-one extension target. -/
abbrev rankOneExtensionCharacter
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier) :
    Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) (ULift.{uW} ℂ) :=
  (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
    (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))

/-- Full Whittaker type transports to the exact lifted scalar action. -/
theorem rankOneExtensionCharacter_isOfWhittakerType
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology;
      UnitaryAdditiveCharacter F.Carrier)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType 0 (standardCharacter ψ 0)
      (rankOneExtensionCharacter.{uF, uW} F χ) := by
  let := F.canonicalTopologicalData.topology
  exact (rankOneWhittakerType p F ψ χ).of_equiv
    (Representation.Equiv.mk ULift.moduleEquiv.symm (by intro g; rfl))

/-- The lifted rank-one action is smooth in the canonical topology. -/
theorem rankOneExtensionCharacter_isSmooth
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology;
      UnitaryAdditiveCharacter F.Carrier)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    IsSmooth (rankOneExtensionCharacter.{uF, uW} F χ) :=
  (rankOneExtensionCharacter_isOfWhittakerType F ψ χ).1.1

end Langlands.RankinSelberg
