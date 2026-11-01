import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalDual
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPairedComparison
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModelDataConvergence
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonStatement

/-! # The actual matrix-to-rank-one gamma functional equation -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped NNReal ENNReal

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker Conductor RankOneIwasawa
open RankOneBox QuotientIntegration

universe uF uV

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance comparisonProofTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance comparisonProofValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance comparisonProofLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance comparisonProofT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance comparisonProofSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance comparisonProofTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance comparisonProofScalarMeasurable : MeasurableSpace F.Carrier := borel _
local instance comparisonProofScalarBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance comparisonProofGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance comparisonProofGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance comparisonProofGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance comparisonProofGLSigmaCompact (n : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (n + 1)
local instance comparisonProofUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (0 + 1) F.Carrier) := borel _
local instance comparisonProofUnipotentBorel :
    BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
local instance comparisonProofQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
local instance comparisonProofQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 2) F.Carrier) V)
  (ℓ : glFunctionals ψ (m + 1) σ)

/-- One actual principal realization gives both literal block comparisons with
one nonzero scalar, once raw Fourier convergence is supplied. -/
theorem pairedMatrixBlockComparison_of_rawIotaConvergence
    (hsd : IsSelfDual ψ ν)
    (hσ : IsOfWhittakerType (m + 1) (standardCharacter ψ (m + 1)) σ)
    (hℓ : ℓ.val ≠ 0)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ))
    (P : Polynomial ℂ)
    (hIota : GodementJacquet.Padic.IotaMatrixAnalyticAssertions F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ) P)
    (hRaw : ∀ (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (ΦHat : GodementJacquet.MatrixTestFunction (m + 1) F.Carrier),
      ∃ b : ℝ, ∀ s : ℂ, b < s.re →
        Integrable (GodementJacquet.matrixIntegrand abv ΦHat
          (s + GodementJacquet.jpssShift (m + 1))
          (GodementJacquet.coefficientIota (glModelFunction ψ (m + 1) σ ℓ w)))
          (generalLinearHaar F.Carrier (m + 1))) :
    PairedMatrixBlockComparison F ψ ν σ ℓ (by omega) := by
  intro w
  obtain ⟨a, K, hK, hp⟩ := exists_principalModelRealization F ψ σ ℓ w hσ.1.1
  let c := F.canonicalTopologicalData.additiveConductor ψ
  let C := boxExtractionConstant F (n := m + 1) (c + a) c a
  refine ⟨boxLatticeTest F (c + a) c a,
    GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ.1.1 ℓ K hK w,
    (C : ℂ), ?_, ?_, ?_⟩
  · exact_mod_cast (ne_of_gt (boxExtractionConstant_pos F hp.2.1 hp.1))
  · obtain ⟨b, hb⟩ := principalOriginalAssertions_of_realization F ψ σ ℓ w hσ.1.1
      K hK hp hMatrix
    refine ⟨b, fun s hs => ?_⟩
    rw [unequalRankIntegralAt_rankOne_one ψ abv ν σ ℓ w
      (unipotentQuotientHaar F.Carrier 0) (unipotentQuotientHaar_isCompatible F.Carrier 0)]
    exact (hb s hs).2
  · intro ΦHat hpair
    obtain ⟨b, hb⟩ := principalDualAssertions_of_rawConvergence F ψ ν σ ℓ w
      (unipotentQuotientHaar F.Carrier 0) (unipotentQuotientHaar_isCompatible F.Carrier 0)
      hsd hσ.1.1 hσ hℓ K hK hp hMatrix P hIota ΦHat hpair (hRaw w ΦHat)
    exact ⟨b, fun s hs => (hb s hs).2⟩

end Padic

/-- The normalized matrix functional equation on the actual coefficient model
gives the full symmetric rank-one gamma factor, in every rank. -/
theorem rankOneMatrixFunctionalEquationComparison :
    RankOneMatrixFunctionalEquationComparisonStatement.{uF, uV} := by
  intro p _ F ψ ν hsd n V _ _ σ hσ ℓ hℓ P PDual c a hData
  cases n with
  | zero =>
    exact rankOneMatrixFunctionalEquationComparison_zero F ψ ν σ hσ ℓ hℓ hData
  | succ m =>
    apply rankOneGammaFactor_of_pairedMatrixComparison F ψ ν σ ℓ (by omega)
      hσ hℓ hsd P PDual c a hData
    apply pairedMatrixBlockComparison_of_rawIotaConvergence F ψ ν σ ℓ
      hsd hσ hℓ hData.1.1 PDual hData.2.1
    intro w ΦHat
    obtain ⟨b, hb⟩ := rawModelIotaMatrixConvergence_of_modelIota
      F ψ σ ℓ w hσ.1.1 hData.2.1.1 ΦHat
    refine ⟨b - (GodementJacquet.jpssShift (m + 1)).re, fun s hs => ?_⟩
    apply hb (s + GodementJacquet.jpssShift (m + 1))
    rw [Complex.add_re]
    linarith

end Langlands.RankinSelberg
