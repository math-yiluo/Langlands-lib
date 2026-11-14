import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonCompactGLParameters
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonScalarHaar
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylOrbitBlocks
/-! Joint compact-parameter convergence before taking the actual orbit average. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement compactParametersBorel compactParametersGLBorel compactParametersGLLocallyCompact compactParametersGLMeasurable compactParametersGLSecondCountable compactParametersLocalField compactParametersMeasurable compactParametersNBorel compactParametersNMeasurable compactParametersSecondCountable compactParametersT2 compactParametersTopology compactParametersTotallyDisconnected compactParametersValuativeRel determinantNorm_rankOneSignedBlockWeyl diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support integrable_generalLinear_one_natWeight_iff integrable_generalLinear_one_prod_natWeight_iff integrable_prod_generalLinear_one_natWeight_iff integral_generalLinear_one_natWeight integral_generalLinear_one_prod_natWeight integral_prod_generalLinear_one_natWeight lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply orbitBlocksBorel orbitBlocksLocalField orbitBlocksMeasurable orbitBlocksNBorel orbitBlocksNLocallyCompact orbitBlocksNMeasurable orbitBlocksNSecondCountable orbitBlocksSecondCountable orbitBlocksSigmaCompact orbitBlocksT2 orbitBlocksTopology orbitBlocksTotallyDisconnected orbitBlocksValuativeRel rankOneModelValues_subset_whittakerRationalValues scalarHaarBorel scalarHaarGLBorel scalarHaarGLLocallyCompact scalarHaarGLMeasurable scalarHaarGLSecondCountable scalarHaarLocalField scalarHaarMeasurable scalarHaarNullSingleton scalarHaarSecondCountable scalarHaarSigmaCompact scalarHaarT2 scalarHaarTopology scalarHaarValuativeRel signedBlockGLParameterIntegrand signedWeylGLParameterIntegrand signedWeylGL_blockGL_parameter_duality signedWeylOrbit_blockOrbit_fourier_duality signedWeylOrbit_blockOrbit_fourier_duality_averaged signedWeyl_affineBlock_fourier_duality singleton_modulus_real unequalRankFiniteExpansion weylBlockBorelSpace weylBlockLocalField weylBlockMeasurableSpace weylBlockNBorelSpace weylBlockNLocallyCompact weylBlockNMeasurableSpace weylBlockNSecondCountable weylBlockSecondCountable weylBlockSigmaCompact weylBlockT2 weylBlockTopology weylBlockTotallyDisconnected weylBlockValuativeRel zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker

universe uF uX

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance compactParametersT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance compactParametersSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance compactParametersMeasurable : MeasurableSpace F := borel _
local instance compactParametersBorel : BorelSpace F := ⟨rfl⟩
local instance compactParametersNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance compactParametersNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance compactParametersGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance compactParametersGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance compactParametersGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace (n + 1)
local instance compactParametersGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)
local instance compactParametersTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- The parameter is retained outside the unipotent orbit integral. -/
def signedWeylGLParameterIntegrand
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (m : ℕ) (U : X → Langlands.GeneralLinear (m + 2) F)
    (κ : SchwartzBruhat X)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F))
    (z : X × Langlands.GeneralLinear 1 F) : ℂ :=
  κ z.1 * (determinantWeight abv z.2 1 *
    ∫ u, signedWeylOrbitFourierKernel ψ ν m (U z.1) Φ (u, z.2 0 0)
      ∂unipotentHaar F (m + 1))

/-- The compact parameter and actual complementary block are both retained. -/
def signedBlockGLParameterIntegrand
    (ψ : UnitaryAdditiveCharacter F)
    (m : ℕ) (U : X → Langlands.GeneralLinear (m + 2) F)
    (κ : SchwartzBruhat X)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F))
    (z : X × (Langlands.GeneralLinear 1 F ×
      Matrix (Fin m) (Fin 1) F)) : ℂ :=
  κ z.1 * (determinantWeight abv z.2.1 1 *
    ∫ u, signedBlockOrbitKernel ψ m (U z.1) Φ (u, (z.2.1 0 0, z.2.2))
      ∂unipotentHaar F (m + 1))

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
private theorem locallyConstant_signedWeylGLParameter_family
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F) (hU : Continuous U)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F)) :
    IsLocallyConstant (fun x => fun g : Langlands.GeneralLinear 1 F =>
      determinantWeight abv g 1 *
        ∫ u, signedWeylOrbitFourierKernel ψ ν m (U x) Φ (u, g 0 0)
          ∂unipotentHaar F (m + 1)) := by
  let Φhat := rectangularFourierEquiv ψ ν (m + 2) (m + 2) hsd Φ
  have ht : IsLocallyConstant (fun x => fun Y :
      Matrix (Fin (m + 2)) (Fin (m + 2)) F =>
      rectangularFourierIntegral ψ ν Φ (Y * (U x).val)) := by
    simpa only [Φhat, rectangularFourierEquiv_apply, Units.val_one,
      Matrix.one_mul] using
      GodementJacquet.isLocallyConstant_matrixTranslate Φhat (fun _ : X => 1) U
        continuous_const hU
  unfold signedWeylOrbitFourierKernel
  exact ht.comp (fun (T : Matrix (Fin (m + 2)) (Fin (m + 2)) F → ℂ)
      (g : Langlands.GeneralLinear 1 F) =>
    determinantWeight abv g 1 *
      ∫ u : upperUnipotent (m + 2) F,
        (inverseStandardCharacter ψ (m + 1) u : ℂ) *
          T ((inverseTranspose (m + 2) F u.val).val *
            (rankOneSignedWeyl (m + 1))⁻¹.val *
            Matrix.diagonal (Fin.cons (g 0 0) (fun _ => 1)))
        ∂unipotentHaar F (m + 1))

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
private theorem locallyConstant_signedBlockGLParameter_family
    (ψ : UnitaryAdditiveCharacter F) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F) (hU : Continuous U)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F)) :
    IsLocallyConstant (fun x => fun z : Langlands.GeneralLinear 1 F ×
        Matrix (Fin m) (Fin 1) F =>
      determinantWeight abv z.1 1 *
        ∫ u, signedBlockOrbitKernel ψ m (U x) Φ (u, (z.1 0 0, z.2))
          ∂unipotentHaar F (m + 1)) := by
  have ht := GodementJacquet.isLocallyConstant_matrixTranslate Φ
    (fun _ : X => 1) (fun x => inverseTranspose (m + 2) F (U x))
    continuous_const ((continuous_inverseTranspose _ _).comp hU)
  have ht' : IsLocallyConstant (fun x => fun Y :
      Matrix (Fin (m + 2)) (Fin (m + 2)) F =>
      Φ (Y * (inverseTranspose (m + 2) F (U x)).val)) := by
    simpa only [Units.val_one, Matrix.one_mul] using ht
  unfold signedBlockOrbitKernel
  exact ht'.comp (fun (T : Matrix (Fin (m + 2)) (Fin (m + 2)) F → ℂ)
      (z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F) =>
    determinantWeight abv z.1 1 *
      ∫ u : upperUnipotent (m + 2) F,
        (inverseStandardCharacter ψ (m + 1) u : ℂ) *
          T (u.val.val * firstColumnMatrix (m + 1) (rankOneAffineParameters m
            (z.1 0 0, z.2)) * (rankOneSignedBlockWeyl (m + 1) (by omega)).val)
        ∂unipotentHaar F (m + 1))

/-- Joint convergence holds before averaging in the compact parameter, on
both the scalar Fourier side and the actual complementary-block side. -/
theorem signedWeylGL_blockGL_parameter_duality
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F) (hU : Continuous U)
    (κ : SchwartzBruhat X)
    (hunit : ∀ x, κ x ≠ 0 →
      (⟨⟩ : LocalFieldData F).determinantNorm (m + 2) (U x) = 1)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F)) :
    Integrable (signedWeylGLParameterIntegrand F ψ ν m U κ Φ)
      (μ.prod (generalLinearHaar F 0)) ∧
    Integrable (signedBlockGLParameterIntegrand F ψ m U κ Φ)
      (μ.prod ((generalLinearHaar F 0).prod (rectangularMeasure ν m 1))) ∧
    (∫ z, signedWeylGLParameterIntegrand F ψ ν m U κ Φ z
      ∂μ.prod (generalLinearHaar F 0)) =
    ∫ z, signedBlockGLParameterIntegrand F ψ m U κ Φ z
      ∂μ.prod ((generalLinearHaar F 0).prod (rectangularMeasure ν m 1)) := by
  let L := fun x => fun g : Langlands.GeneralLinear 1 F =>
    determinantWeight abv g 1 *
      ∫ u, signedWeylOrbitFourierKernel ψ ν m (U x) Φ (u, g 0 0)
        ∂unipotentHaar F (m + 1)
  let R := fun x => fun z : Langlands.GeneralLinear 1 F ×
      Matrix (Fin m) (Fin 1) F =>
    determinantWeight abv z.1 1 *
      ∫ u, signedBlockOrbitKernel ψ m (U x) Φ (u, (z.1 0 0, z.2))
        ∂unipotentHaar F (m + 1)
  have hlsec (x : X) : Integrable (fun g => κ x * L x g)
      (generalLinearHaar F 0) := by
    by_cases hx : κ x = 0
    · simp only [hx, zero_mul]
      exact integrable_zero _ _ _
    · have hi := (signedWeylOrbit_blockOrbit_fourier_duality_averaged
        F ψ ν hsd m (U x) (hunit x hx) Φ).1
      exact ((integrable_generalLinear_one_natWeight_iff F ν _).2 hi).const_mul _
  have hrsec (x : X) : Integrable (fun z => κ x * R x z)
      ((generalLinearHaar F 0).prod (rectangularMeasure ν m 1)) := by
    by_cases hx : κ x = 0
    · simp only [hx, zero_mul]
      exact integrable_zero _ _ _
    · have hi := (signedWeylOrbit_blockOrbit_fourier_duality_averaged
        F ψ ν hsd m (U x) (hunit x hx) Φ).2.1
      exact ((integrable_generalLinear_one_prod_natWeight_iff
        F (rectangularMeasure ν m 1) ν _).2 hi).const_mul _
  have hl0 := integrable_compact_locallyConstant_family μ _
    (fun x => κ x • L x)
    (κ.locallyConstant.comp₂
      (locallyConstant_signedWeylGLParameter_family F ψ ν hsd m U hU Φ)
      (fun c T => c • T))
    κ.hasCompactSupport.smul_right hlsec
  have hr0 := integrable_compact_locallyConstant_family μ _
    (fun x => κ x • R x)
    (κ.locallyConstant.comp₂
      (locallyConstant_signedBlockGLParameter_family F ψ m U hU Φ)
      (fun c T => c • T))
    κ.hasCompactSupport.smul_right hrsec
  have hl : Integrable (signedWeylGLParameterIntegrand F ψ ν m U κ Φ)
      (μ.prod (generalLinearHaar F 0)) := by
    change Integrable (fun z : X × Langlands.GeneralLinear 1 F =>
      κ z.1 * L z.1 z.2) (μ.prod (generalLinearHaar F 0))
    simpa only [Pi.smul_apply, smul_eq_mul] using hl0
  have hr : Integrable (signedBlockGLParameterIntegrand F ψ m U κ Φ)
      (μ.prod ((generalLinearHaar F 0).prod (rectangularMeasure ν m 1))) := by
    change Integrable (fun z : X × (Langlands.GeneralLinear 1 F ×
      Matrix (Fin m) (Fin 1) F) => κ z.1 * R z.1 z.2)
      (μ.prod ((generalLinearHaar F 0).prod (rectangularMeasure ν m 1)))
    simpa only [Pi.smul_apply, smul_eq_mul] using hr0
  refine ⟨hl, hr, ?_⟩
  rw [integral_prod _ hl, integral_prod _ hr]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : κ x = 0
  · simp only [signedWeylGLParameterIntegrand, signedBlockGLParameterIntegrand,
      hx, zero_mul, integral_zero]
  · simp only [signedWeylGLParameterIntegrand, signedBlockGLParameterIntegrand,
      integral_const_mul]
    congr 1
    let A : F → ℂ := fun a => ∫ u,
      signedWeylOrbitFourierKernel ψ ν m (U x) Φ (u, a)
        ∂unipotentHaar F (m + 1)
    let B : F × Matrix (Fin m) (Fin 1) F → ℂ := fun z => ∫ u,
      signedBlockOrbitKernel ψ m (U x) Φ (u, z)
        ∂unipotentHaar F (m + 1)
    obtain ⟨_, hb, he⟩ := signedWeylOrbit_blockOrbit_fourier_duality_averaged
      F ψ ν hsd m (U x) (hunit x hx) Φ
    exact (integral_generalLinear_one_natWeight F ν A).trans
      ((congrArg (fun t : ℂ =>
        ((Langlands.AllField.RankinSelberg.GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) : ℂ)⁻¹ * t)
        (he.trans (integral_prod B hb).symm)).trans
          (integral_generalLinear_one_prod_natWeight F (rectangularMeasure ν m 1) ν B).symm)

end Langlands.AllField.RankinSelberg
