import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedDualBlock
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalOriginal

/-! # The actual complementary dual value with the original box constant -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped NNReal ENNReal

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker Conductor RankOneIwasawa
open RankOneBox QuotientIntegration

universe uF uV
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance principalDualTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance principalDualValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance principalDualLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance principalDualT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance principalDualSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance principalDualTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance principalDualScalarMeasurable : MeasurableSpace F.Carrier := borel _
local instance principalDualScalarBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance principalDualGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance principalDualGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance principalDualGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance principalDualGLSigmaCompact (n : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (n + 1)
local instance principalDualUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (0 + 1) F.Carrier) := borel _
local instance principalDualUnipotentBorel :
    BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
local instance principalDualQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
local instance principalDualQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 2) F.Carrier) V)
  (ℓ : glFunctionals ψ (m + 1) σ)
  (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
  (μ : Measure (LeftUnipotentQuotient 0 F.Carrier))
  (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier) (generalLinearHaar F.Carrier 0)
    (unipotentHaar F.Carrier 0) μ)

include hμ in
/-- The Fourier matrix value of an original principal-fixed vector is the same
box scalar times its literal complementary dual, under genuine convergence. -/
theorem principalDual_value
    (hsd : IsSelfDual ψ ν) (hσ : IsSmooth σ) {a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ F.canonicalTopologicalData.additiveConductor ψ + a)
    (hfixed : ∀ k ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * k) = glModelFunction ψ (m + 1) σ ℓ w g)
    (ΦHat : GodementJacquet.MatrixTestFunction (m + 1) F.Carrier)
    (hpair : GodementJacquet.Padic.MatrixFourierPair F ψ ν
      (boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a) ΦHat)
    (s : ℂ)
    (hi : Integrable (GodementJacquet.matrixIntegrand abv ΦHat
      (s + GodementJacquet.jpssShift (m + 1))
      (GodementJacquet.coefficientIota (glModelFunction ψ (m + 1) σ ℓ w)))
      (generalLinearHaar F.Carrier (m + 1)))
    (hj : Integrable (rankOneDualBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ w))
      ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1))) :
    GodementJacquet.matrixIntegral abv (generalLinearHaar F.Carrier (m + 1)) ΦHat
      (s + GodementJacquet.jpssShift (m + 1))
      (GodementJacquet.coefficientIota (glModelFunction ψ (m + 1) σ ℓ w)) =
    (boxExtractionConstant F (n := m + 1)
      (F.canonicalTopologicalData.additiveConductor ψ + a)
      (F.canonicalTopologicalData.additiveConductor ψ) a : ℂ) *
      dualUnequalRankModelIntegralAt (by omega) 0 m (by omega) ψ abv μ ν σ
        (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ)
        w (rankOneTrivialModelOne ψ) s := by
  obtain ⟨wd, hwd⟩ := exists_rankOneSignedDualModel ψ σ ℓ w
  have he : glModelFunction ψ (m + 1) (inverseTransposePullback σ)
      (rankOneSignedDualFunctional ψ σ ℓ) wd =
      rankOneSignedDualFunction (m + 1) (glModelFunction ψ (m + 1) σ ℓ w) := funext hwd
  have hdfixed := rankOneSignedDualFunction_principalFixed (m + 1) a
    (glModelFunction ψ (m + 1) σ ℓ w) hfixed
  have hdi := (integrable_principalModelFourierIntegrand_signedDual_iff F ψ ν m a
    (s + GodementJacquet.jpssShift (m + 1))
    (glModelFunction ψ (m + 1) σ ℓ w) ΦHat hpair).mpr hi
  have hdj := (integrable_principalFixedBlockIntegrand_signedDual_iff F ν m s
    (glModelFunction ψ (m + 1) σ ℓ w)).mpr hj
  have hv := principalFixedModelDual_pairing F ψ ν hsd ha hA
    (inverseTransposePullback σ) (inverseTransposePullback_isSmooth σ hσ)
    (rankOneSignedDualFunctional ψ σ ℓ) wd
    (s + GodementJacquet.jpssShift (m + 1))
    (by rw [he]; exact hdfixed) (by rw [he]; exact hdi) (by rw [he]; exact hdj)
  rw [he, integral_principalModelFourierIntegrand_signedDual F ψ ν m a
      (s + GodementJacquet.jpssShift (m + 1)) _ ΦHat hpair,
    integral_principalFixedBlockIntegrand_signedDual F ν m s,
    integral_rankOneDualBlockIntegrand F ψ ν σ ℓ w μ hμ s hj] at hv
  exact hv

/-- The Fourier half-plane assertions for the very same principal realization.
Raw convergence is retained separately from the averaged coefficient value. -/
def PrincipalDualAssertions (hσ : IsSmooth σ) (a : ℕ)
    (K : OpenSubgroup (Langlands.GeneralLinear (m + 2) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 2) F.Carrier)))
    (ΦHat : GodementJacquet.MatrixTestFunction (m + 1) F.Carrier) : Prop :=
  let c := F.canonicalTopologicalData.additiveConductor ψ
  let f := GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w
  let C := boxExtractionConstant F (n := m + 1) (c + a) c a
  ∃ b : ℝ, ∀ s : ℂ, b < s.re →
    Integrable (GodementJacquet.matrixIntegrand abv ΦHat
      (s + GodementJacquet.jpssShift (m + 1))
      (GodementJacquet.coefficientIota (glModelFunction ψ (m + 1) σ ℓ w)))
      (generalLinearHaar F.Carrier (m + 1)) ∧
    GodementJacquet.matrixIntegral abv (generalLinearHaar F.Carrier (m + 1)) ΦHat
      (s + GodementJacquet.jpssShift (m + 1)) (GodementJacquet.coefficientIota f.val) =
      (C : ℂ) * dualUnequalRankModelIntegralAt (by omega) 0 m (by omega) ψ abv μ ν σ
        (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ)
        w (rankOneTrivialModelOne ψ) s

include hμ in
/-- Original and raw Fourier convergence together with the supplied transformed
matrix data give the dual assertions for the same averaged coefficient. -/
theorem principalDualAssertions_of_rawConvergence
    (hsd : IsSelfDual ψ ν) (hσ : IsSmooth σ)
    (hwt : IsOfWhittakerType (m + 1) (standardCharacter ψ (m + 1)) σ)
    (hℓ : ℓ.val ≠ 0) {a : ℕ}
    (K : OpenSubgroup (Langlands.GeneralLinear (m + 2) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 2) F.Carrier)))
    (hp : PrincipalModelRealization F ψ σ ℓ w hσ a K hK)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ))
    (P : Polynomial ℂ)
    (hIota : GodementJacquet.Padic.IotaMatrixAnalyticAssertions F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ) P)
    (ΦHat : GodementJacquet.MatrixTestFunction (m + 1) F.Carrier)
    (hpair : GodementJacquet.Padic.MatrixFourierPair F ψ ν
      (boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a) ΦHat)
    (hRaw : ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      Integrable (GodementJacquet.matrixIntegrand abv ΦHat
        (s + GodementJacquet.jpssShift (m + 1))
        (GodementJacquet.coefficientIota (glModelFunction ψ (m + 1) σ ℓ w)))
        (generalLinearHaar F.Carrier (m + 1))) :
    PrincipalDualAssertions F ψ ν σ ℓ w μ hσ a K hK ΦHat := by
  obtain ⟨bo, hbo⟩ := principalOriginalAssertions_of_realization F ψ σ ℓ w hσ K hK hp hMatrix
  obtain ⟨bd, hbd⟩ := hRaw
  obtain ⟨bj, hbj⟩ := rankOneDualBlock_convergesOnRight_of_iota F ψ ν σ ℓ μ hμ hwt hℓ P hIota
  have hΦHat := GodementJacquet.Padic.compactOpen_matrixTest_fourier_invariant F ψ ν K hK
    _ ΦHat hpair (fun k hk => (hp.2.2.2.2.1 k hk).1)
  refine ⟨max bo (max bd bj), fun s hs => ?_⟩
  have hso : bo < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsdj : max bd bj < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have hsd' : bd < s.re := lt_of_le_of_lt (le_max_left _ _) hsdj
  have hsj : bj < s.re := lt_of_le_of_lt (le_max_right _ _) hsdj
  have hi := hbd s hsd'
  have hav := GodementJacquet.Padic.averagedModelCoefficient_paired_integrals F ψ σ hσ ℓ K hK
    _ ΦHat hp.2.2.2.2.1 hΦHat w
    (s + GodementJacquet.jpssShift (m + 1)) (s + GodementJacquet.jpssShift (m + 1))
    (hbo s hso).1 hi
  exact ⟨hi, hav.2.2.2.trans (principalDual_value F ψ ν σ ℓ w μ hμ hsd hσ hp.1 hp.2.1
    hp.2.2.1 ΦHat hpair s hi (hbj w s hsj))⟩

end Langlands.RankinSelberg
