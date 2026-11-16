import Langlands.Representation.Conductor.SupercuspidalPadicConductorExponentStatement
import Langlands.Representation.Conductor.GenericEpsilonConductor

/-!
# The generic conductor from the supercuspidal p-adic conductor premise

This specializes the comparison with the JPSS newvector conductor to a supercuspidal
representation over a p-adic field, using only the correspondingly restricted premise.
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg GeneralLinear

universe uF uV

private theorem supercuspidalPadic_valuative_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance supercuspidalPadicGenericNormedField : NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField
local instance supercuspidalPadicGenericValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance supercuspidalPadicGenericLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance supercuspidalPadicGenericNonarchimedeanAddGroup :
    NonarchimedeanAddGroup F.Carrier := supercuspidalPadic_valuative_nonarchimedean
local instance supercuspidalPadicGenericMeasurableSpace : MeasurableSpace F.Carrier :=
  borel F.Carrier
local instance supercuspidalPadicGenericBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩

/-- For a generic supercuspidal representation over a p-adic field and a character
of conductor `𝔒`, the restricted conductor premise identifies the constructed
generic conductor with a natural newvector level, whose fixed space is a line. -/
theorem genericConductor_isNewvectorConductor_of_supercuspidalPadic
    (hC : SupercuspidalPadicConductorExponentStatement.{uF, uV})
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier) (hψ : HasIntegerConductor ψ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hπ : Whittaker.IsGeneric ψ r π) (hsc : GeneralLinear.IsSupercuspidal π) :
    ∃ m : ℕ, genericConductor F ψ π hπ = m ∧ IsNewvectorConductor π m ∧
      Module.finrank ℂ (levelFixedVectors π m) = 1 := by
  obtain ⟨ϖ, hϖ, hϖabs⟩ := HighlyRamified.exists_uniformizingElement_normalizedAbs F
  obtain ⟨c, m, hε, hnew, hdim⟩ := @hC p _ F (show T2Space F.Carrier from inferInstance)
    (show TotallyDisconnectedSpace F.Carrier from inferInstance) (borel F.Carrier) ⟨rfl⟩
    (borel _) (@BorelSpace.mk _ _ (borel _) rfl) (borel _) (@BorelSpace.mk _ _ (borel _) rfl)
    (borel _) (@BorelSpace.mk _ _ (borel _) rfl)
    F.canonicalTopologicalData.residueCardinality rfl
    (normalizedAbsoluteValue F.canonicalTopologicalData) ϖ hϖ hϖabs
    (HighlyRamified.normalizedAbsoluteValue_eq_one F) ψ hψ
    (Correspondence.localSelfDualHaar F ψ) (Correspondence.isSelfDual_localSelfDualHaar F ψ)
    r V _ _ π hπ hsc
  exact ⟨m, genericConductor_eq_of_hasIntegerConductor F ψ π hπ hψ _
    (Correspondence.isSelfDual_localSelfDualHaar F ψ) hε, hnew, hdim⟩

end Langlands.Conductor
