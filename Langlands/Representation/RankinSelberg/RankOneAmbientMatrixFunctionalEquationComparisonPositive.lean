import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonProof

/-! # Positive-rank comparison using ambient matrix data -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped NNReal ENNReal

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker Conductor RankOneIwasawa
open RankOneBox QuotientIntegration

universe uF uV uW

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance ambientComparisonTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance ambientComparisonValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance ambientComparisonLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance ambientComparisonT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance ambientComparisonSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance ambientComparisonTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance ambientComparisonScalarMeasurable : MeasurableSpace F.Carrier := borel _
local instance ambientComparisonScalarBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance ambientComparisonGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance ambientComparisonGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance ambientComparisonGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance ambientComparisonGLSigmaCompact (n : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (n + 1)
local instance ambientComparisonUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (0 + 1) F.Carrier) := borel _
local instance ambientComparisonUnipotentBorel :
    BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
local instance ambientComparisonQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
local instance ambientComparisonQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

namespace AmbientMatrixComparison

section AnyRank

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ)

/-- View the identical actual model coefficient in the supplied ambient family. -/
def coefficient {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)
    (hinc : GodementJacquet.biSmoothMatrixCoefficients
        (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
        (glModelRepresentation ψ r σ ℓ) ≤ GodementJacquet.biSmoothMatrixCoefficients ρ)
    (f : GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (glModelRepresentation ψ r σ ℓ)) : GodementJacquet.biSmoothMatrixCoefficients ρ :=
  ⟨f.val, hinc f.property⟩

/-- Inverse-transpose convergence alone gives ordinary convergence of the
actual first-dual model; no assertion about normalized generators is used. -/
theorem firstDualMatrixConvergesOnRight
    (hIota : GodementJacquet.Padic.IotaMatrixConvergesOnRight F
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (glModelRepresentation ψ r σ ℓ)) :
    GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel (ψ.scale (-1)) r (inverseTransposePullback σ)
        (firstDualFunctional ψ σ ℓ)).toSubmodule)
      (glModelRepresentation (ψ.scale (-1)) r (inverseTransposePullback σ)
        (firstDualFunctional ψ σ ℓ)) := by
  have hM := @matrixConvergesOnRight_inverseTransposePullback
    p _ F r (glCoefficientModel ψ r σ ℓ).toSubmodule inferInstance inferInstance
    (glModelRepresentation ψ r σ ℓ) hIota
  unfold GodementJacquet.Padic.MatrixConvergesOnRight
    GodementJacquet.MatrixConvergesOnRight at hM ⊢
  have he := @GodementJacquet.biSmoothMatrixCoefficients_equiv
    (Langlands.GeneralLinear (r + 1) F.Carrier) inferInstance inferInstance
    (glCoefficientModel ψ r σ ℓ).toSubmodule inferInstance inferInstance
    (glCoefficientModel (ψ.scale (-1)) r (inverseTransposePullback σ)
      (firstDualFunctional ψ σ ℓ)).toSubmodule inferInstance inferInstance
    _ _ (firstDualModelRepresentationEquiv ψ σ ℓ)
  rw [← he]
  exact hM

/-- Actual complementary-dual convergence follows from the restricted common
inverse-transpose bound, independently of ambient generators. -/
theorem dualBlockZeroConvergesOnRight (hrpos : 0 < r)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (hℓ : ℓ.val ≠ 0)
    (μ : Measure (LeftUnipotentQuotient 0 F.Carrier))
    (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier) (generalLinearHaar F.Carrier 0)
      (unipotentHaar F.Carrier 0) μ)
    (hIota : GodementJacquet.Padic.IotaMatrixConvergesOnRight F
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (glModelRepresentation ψ r σ ℓ)) :
    ∃ b : ℝ, ∀ f : (coefficientModel σ ℓ).toSubmodule,
      ∀ s : ℂ, b < s.re →
      UnequalRankConverges (ψ.scale (-1)) abv (r - 0 - 1) 0 μ
        (rectangularMeasure ν (r - 0 - 1) (0 + 1))
        (InducedTailIntermediate.whittakerRankCast (ψ.scale (-1)) (by omega)
          (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f.val)
            (blockWeylAt 0 r hrpos)))
        (secondDualFunction ψ 0 (rankOneTrivialModelOne ψ).val) s := by
  have hMd := firstDualMatrixConvergesOnRight F ψ σ ℓ hIota
  have hconv := RankOneBlockConvergence.allBlocksConvergeOnRight_of_matrix F
    (ψ.scale (-1)) ν (inverseTransposePullback σ) (firstDualFunctional ψ σ ℓ)
    (isOfWhittakerType_firstDual ψ σ hσ) (firstDualFunctional_ne_zero ψ σ hℓ)
    μ hμ hMd (r - 0 - 1) 0 (by omega)
  have h1 : secondDualFunction ψ 0 (rankOneTrivialModelOne ψ).val =
      (rankOneTrivialModelOne (ψ.scale (-1))).val := by
    apply Subtype.ext
    funext g
    simp only [secondDualFunction_apply, rankOneTrivialModelOne_apply]
  obtain ⟨b, hb⟩ := hconv
  refine ⟨b, fun f s hs => ?_⟩
  rw [h1]
  exact hb (translatedFirstDualModelEquiv ψ σ ℓ (blockWeylAt 0 r hrpos) f) s hs

end AnyRank

section Positive

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 2) F.Carrier) V)
  (ℓ : glFunctionals ψ (m + 1) σ)
  (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
  (μ : Measure (LeftUnipotentQuotient 0 F.Carrier))
  (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier) (generalLinearHaar F.Carrier 0)
    (unipotentHaar F.Carrier 0) μ)

include hμ in
/-- The actual signed-dual block has a common right half-plane using only
inverse-transpose coefficient convergence. -/
theorem rankOneDualBlockConvergesOnRight
    (hσ : IsOfWhittakerType (m + 1) (standardCharacter ψ (m + 1)) σ) (hℓ : ℓ.val ≠ 0)
    (hIota : GodementJacquet.Padic.IotaMatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ)) :
    ∃ b : ℝ, ∀ v : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
      ∀ s : ℂ, b < s.re →
        Integrable (rankOneDualBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ v))
          ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1)) := by
  obtain ⟨b, hb⟩ := dualBlockZeroConvergesOnRight
    F ψ ν σ ℓ (by omega) hσ hℓ μ hμ hIota
  refine ⟨b, fun v s hs => ?_⟩
  apply (integrable_rankOneDualBlockIntegrand_iff F ψ ν σ ℓ v μ hμ s).mpr
  have he : m + 1 - 0 - 1 = m := by omega
  have H : ∃ hr : m + 1 = 0 + ((m + 1 - 0 - 1) + 0 + 1),
      UnequalRankConverges (ψ.scale (-1)) abv (m + 1 - 0 - 1) 0 μ
        (rectangularMeasure ν (m + 1 - 0 - 1) 1)
        (InducedTailIntermediate.whittakerRankCast (ψ.scale (-1)) hr
          (translateWhittaker (ψ.scale (-1)) (m + 1) (firstDualFunction ψ (m + 1) v.val)
            (blockWeylAt 0 (m + 1) (by omega))))
        (secondDualFunction ψ 0 (rankOneTrivialModelOne ψ).val) s :=
    ⟨_, hb v s hs⟩
  rw [he] at H
  exact H.choose_spec


include hμ in
/-- The principal dual comparison uses genuine common convergence alone;
its Fourier test and extraction scalar are unchanged. -/
theorem principalDualAssertions
    (hsd : IsSelfDual ψ ν) (hσ : IsSmooth σ)
    (hwt : IsOfWhittakerType (m + 1) (standardCharacter ψ (m + 1)) σ)
    (hℓ : ℓ.val ≠ 0) {a : ℕ}
    (K : OpenSubgroup (Langlands.GeneralLinear (m + 2) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 2) F.Carrier)))
    (hp : PrincipalModelRealization F ψ σ ℓ w hσ a K hK)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ))
    (hIota : GodementJacquet.Padic.IotaMatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ))
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
  obtain ⟨bj, hbj⟩ := rankOneDualBlockConvergesOnRight F ψ ν σ ℓ μ hμ hwt hℓ hIota
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


/-- One principal realization compares the literal original and complementary
dual blocks to the same actual coefficient, using only convergence. -/
theorem pairedMatrixBlockComparison
    (hsd : IsSelfDual ψ ν)
    (hσ : IsOfWhittakerType (m + 1) (standardCharacter ψ (m + 1)) σ)
    (hℓ : ℓ.val ≠ 0)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ))
    (hIota : GodementJacquet.Padic.IotaMatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ))
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
    obtain ⟨b, hb⟩ := principalDualAssertions F ψ ν σ ℓ w
      (unipotentQuotientHaar F.Carrier 0) (unipotentQuotientHaar_isCompatible F.Carrier 0)
      hsd hσ.1.1 hσ hℓ K hK hp hMatrix hIota ΦHat hpair (hRaw w ΦHat)
    exact ⟨b, fun s hs => (hb s hs).2⟩


/-- Ambient matrix data and actual coefficient inclusion give the complete
positive-rank gamma certificate for the original representation. -/
theorem gammaFactor
    (hsd : IsSelfDual ψ ν)
    (hσ : IsOfWhittakerType (m + 1) (standardCharacter ψ (m + 1)) σ)
    (hℓ : ℓ.val ≠ 0)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Langlands.GeneralLinear (m + 2) F.Carrier) W)
    (hinc : GodementJacquet.biSmoothMatrixCoefficients
        (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
        (glModelRepresentation ψ (m + 1) σ ℓ) ≤
      GodementJacquet.biSmoothMatrixCoefficients ρ)
    {P PDual : Polynomial ℂ} {c : ℂˣ} {a : ℤ}
    (hData : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
      ρ P PDual c a) :
    IsPadicSymmetricGammaFactor F ψ ν σ (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
      (rationalGammaExpression (LocalFactor.residueReflection F) c a P PDual) := by
  have hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ) := by
    obtain ⟨b, hb⟩ := hData.1.1
    exact ⟨b, fun Φ f s hs => hb Φ (coefficient F ψ σ ℓ ρ hinc f) s hs⟩
  have hIota : GodementJacquet.Padic.IotaMatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ) := by
    obtain ⟨b, hb⟩ := hData.2.1.1
    exact ⟨b, fun Φ f s hs => hb Φ (coefficient F ψ σ ℓ ρ hinc f) s hs⟩
  have hComparison : PairedMatrixBlockComparison F ψ ν σ ℓ (by omega) := by
    apply pairedMatrixBlockComparison F ψ ν σ ℓ hsd hσ hℓ hMatrix hIota
    intro w ΦHat
    obtain ⟨b, hb⟩ := rawModelIotaMatrixConvergence_of_modelIota
      F ψ σ ℓ w hσ.1.1 hIota ΦHat
    refine ⟨b - (GodementJacquet.jpssShift (m + 1)).re, fun s hs => ?_⟩
    apply hb (s + GodementJacquet.jpssShift (m + 1))
    rw [Complex.add_re]
    linarith
  apply rankOneGammaFactor_of_normalized_blockZero_one F ψ ν σ hσ ℓ hℓ
    (by omega) hsd hData.2.1.2.2.polynomial_ne_zero
  intro w
  obtain ⟨Φ, f, C, hC, he, hed⟩ := hComparison w
  obtain ⟨ΦHat, hpair, hFE⟩ := hData.2.2 Φ
  let fc := coefficient F ψ σ ℓ ρ hinc f
  obtain ⟨RM, hRM⟩ := hData.1.2.1 Φ fc
  obtain ⟨RMd, hRMd⟩ := hData.2.1.2.1 ΦHat fc
  let R := RatFunc.C C⁻¹ * RM
  let Rd := RatFunc.C C⁻¹ * RMd
  refine ⟨R, Rd, ?_, ?_, ?_⟩
  · apply RationalContinuationLinear.continuation_of_eq_on_right
      (hasRationalContinuation_const_mul C⁻¹ hRM.2)
    obtain ⟨b, hb⟩ := he
    refine ⟨b, fun s hs => ?_⟩
    change _ = C⁻¹ * GodementJacquet.matrixIntegral abv
      (generalLinearHaar F.Carrier (m + 1)) Φ
      (s + GodementJacquet.jpssShift (m + 1)) f.val
    rw [hb s hs, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  · apply RationalContinuationLinear.continuation_of_eq_on_right
      (hasRationalContinuation_const_mul C⁻¹ hRMd.2)
    obtain ⟨b, hb⟩ := hed ΦHat hpair
    refine ⟨b, fun s hs => ?_⟩
    change _ = C⁻¹ * GodementJacquet.matrixIntegral abv
      (generalLinearHaar F.Carrier (m + 1)) ΦHat
      (s + GodementJacquet.jpssShift (m + 1)) (GodementJacquet.coefficientIota f.val)
    rw [hb s hs, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  · have hN := hFE fc RM RMd hRM hRMd
    have hEqR : RM = RatFunc.C C * R := by
      dsimp [R]
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hC, map_one, one_mul]
    have hEqRd : RMd = RatFunc.C C * Rd := by
      dsimp [Rd]
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hC, map_one, one_mul]
    rw [hEqR, hEqRd] at hN
    exact hN.of_const_mul C hC

end Positive

end AmbientMatrixComparison
end Padic
end Langlands.RankinSelberg
