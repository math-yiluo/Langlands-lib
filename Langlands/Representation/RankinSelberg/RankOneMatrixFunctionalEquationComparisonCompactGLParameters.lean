import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonCompactOrbitGL

/-! Joint compact-parameter convergence before taking the actual orbit average. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker Topology

universe uF uX

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance compactParametersTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance compactParametersValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance compactParametersLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance compactParametersT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance compactParametersSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance compactParametersMeasurable : MeasurableSpace F.Carrier := borel _
local instance compactParametersBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance compactParametersNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance compactParametersNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance compactParametersNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance compactParametersGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance compactParametersGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance compactParametersGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance compactParametersGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance compactParametersNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance compactParametersTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- The parameter is retained outside the unipotent orbit integral. -/
def signedWeylGLParameterIntegrand
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (m : ℕ) (U : X → Langlands.GeneralLinear (m + 2) F.Carrier)
    (κ : SchwartzBruhat X)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier))
    (z : X × Langlands.GeneralLinear 1 F.Carrier) : ℂ :=
  κ z.1 * (determinantWeight abv z.2 1 *
    ∫ u, signedWeylOrbitFourierKernel ψ ν m (U z.1) Φ (u, z.2 0 0)
      ∂unipotentHaar F.Carrier (m + 1))

/-- The compact parameter and actual complementary block are both retained. -/
def signedBlockGLParameterIntegrand
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (m : ℕ) (U : X → Langlands.GeneralLinear (m + 2) F.Carrier)
    (κ : SchwartzBruhat X)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier))
    (z : X × (Langlands.GeneralLinear 1 F.Carrier ×
      Matrix (Fin m) (Fin 1) F.Carrier)) : ℂ :=
  κ z.1 * (determinantWeight abv z.2.1 1 *
    ∫ u, signedBlockOrbitKernel ψ m (U z.1) Φ (u, (z.2.1 0 0, z.2.2))
      ∂unipotentHaar F.Carrier (m + 1))

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
private theorem locallyConstant_signedWeylGLParameter_family
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F.Carrier) (hU : Continuous U)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier)) :
    IsLocallyConstant (fun x => fun g : Langlands.GeneralLinear 1 F.Carrier =>
      determinantWeight abv g 1 *
        ∫ u, signedWeylOrbitFourierKernel ψ ν m (U x) Φ (u, g 0 0)
          ∂unipotentHaar F.Carrier (m + 1)) := by
  let Φhat := rectangularFourierEquiv ψ ν (m + 2) (m + 2) hsd Φ
  have ht : IsLocallyConstant (fun x => fun Y :
      Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier =>
      rectangularFourierIntegral ψ ν Φ (Y * (U x).val)) := by
    simpa only [Φhat, rectangularFourierEquiv_apply, Units.val_one,
      Matrix.one_mul] using
      GodementJacquet.isLocallyConstant_matrixTranslate Φhat (fun _ : X => 1) U
        continuous_const hU
  unfold signedWeylOrbitFourierKernel
  exact ht.comp (fun (T : Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier → ℂ)
      (g : Langlands.GeneralLinear 1 F.Carrier) =>
    determinantWeight abv g 1 *
      ∫ u : upperUnipotent (m + 2) F.Carrier,
        (inverseStandardCharacter ψ (m + 1) u : ℂ) *
          T ((inverseTranspose (m + 2) F.Carrier u.val).val *
            (rankOneSignedWeyl (m + 1))⁻¹.val *
            Matrix.diagonal (Fin.cons (g 0 0) (fun _ => 1)))
        ∂unipotentHaar F.Carrier (m + 1))

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
private theorem locallyConstant_signedBlockGLParameter_family
    (ψ : UnitaryAdditiveCharacter F.Carrier) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F.Carrier) (hU : Continuous U)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier)) :
    IsLocallyConstant (fun x => fun z : Langlands.GeneralLinear 1 F.Carrier ×
        Matrix (Fin m) (Fin 1) F.Carrier =>
      determinantWeight abv z.1 1 *
        ∫ u, signedBlockOrbitKernel ψ m (U x) Φ (u, (z.1 0 0, z.2))
          ∂unipotentHaar F.Carrier (m + 1)) := by
  have ht := GodementJacquet.isLocallyConstant_matrixTranslate Φ
    (fun _ : X => 1) (fun x => inverseTranspose (m + 2) F.Carrier (U x))
    continuous_const ((continuous_inverseTranspose _ _).comp hU)
  have ht' : IsLocallyConstant (fun x => fun Y :
      Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier =>
      Φ (Y * (inverseTranspose (m + 2) F.Carrier (U x)).val)) := by
    simpa only [Units.val_one, Matrix.one_mul] using ht
  unfold signedBlockOrbitKernel
  exact ht'.comp (fun (T : Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier → ℂ)
      (z : Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier) =>
    determinantWeight abv z.1 1 *
      ∫ u : upperUnipotent (m + 2) F.Carrier,
        (inverseStandardCharacter ψ (m + 1) u : ℂ) *
          T (u.val.val * firstColumnMatrix (m + 1) (rankOneAffineParameters m
            (z.1 0 0, z.2)) * (rankOneSignedBlockWeyl (m + 1) (by omega)).val)
        ∂unipotentHaar F.Carrier (m + 1))

/-- Joint convergence holds before averaging in the compact parameter, on
both the scalar Fourier side and the actual complementary-block side. -/
theorem signedWeylGL_blockGL_parameter_duality
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F.Carrier) (hU : Continuous U)
    (κ : SchwartzBruhat X)
    (hunit : ∀ x, κ x ≠ 0 →
      F.canonicalTopologicalData.determinantNorm (m + 2) (U x) = 1)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier)) :
    Integrable (signedWeylGLParameterIntegrand F ψ ν m U κ Φ)
      (μ.prod (generalLinearHaar F.Carrier 0)) ∧
    Integrable (signedBlockGLParameterIntegrand F ψ m U κ Φ)
      (μ.prod ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1))) ∧
    (∫ z, signedWeylGLParameterIntegrand F ψ ν m U κ Φ z
      ∂μ.prod (generalLinearHaar F.Carrier 0)) =
    ∫ z, signedBlockGLParameterIntegrand F ψ m U κ Φ z
      ∂μ.prod ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1)) := by
  let L := fun x => fun g : Langlands.GeneralLinear 1 F.Carrier =>
    determinantWeight abv g 1 *
      ∫ u, signedWeylOrbitFourierKernel ψ ν m (U x) Φ (u, g 0 0)
        ∂unipotentHaar F.Carrier (m + 1)
  let R := fun x => fun z : Langlands.GeneralLinear 1 F.Carrier ×
      Matrix (Fin m) (Fin 1) F.Carrier =>
    determinantWeight abv z.1 1 *
      ∫ u, signedBlockOrbitKernel ψ m (U x) Φ (u, (z.1 0 0, z.2))
        ∂unipotentHaar F.Carrier (m + 1)
  have hlsec (x : X) : Integrable (fun g => κ x * L x g)
      (generalLinearHaar F.Carrier 0) := by
    by_cases hx : κ x = 0
    · simp only [hx, zero_mul]
      exact integrable_zero _ _ _
    · have hi := (signedWeylOrbit_blockOrbit_fourier_duality_averaged
        F ψ ν hsd m (U x) (hunit x hx) Φ).1
      exact ((integrable_generalLinear_one_natWeight_iff F ν _).2 hi).const_mul _
  have hrsec (x : X) : Integrable (fun z => κ x * R x z)
      ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1)) := by
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
      (μ.prod (generalLinearHaar F.Carrier 0)) := by
    change Integrable (fun z : X × Langlands.GeneralLinear 1 F.Carrier =>
      κ z.1 * L z.1 z.2) (μ.prod (generalLinearHaar F.Carrier 0))
    simpa only [Pi.smul_apply, smul_eq_mul] using hl0
  have hr : Integrable (signedBlockGLParameterIntegrand F ψ m U κ Φ)
      (μ.prod ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1))) := by
    change Integrable (fun z : X × (Langlands.GeneralLinear 1 F.Carrier ×
      Matrix (Fin m) (Fin 1) F.Carrier) => κ z.1 * R z.1 z.2)
      (μ.prod ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1)))
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
    let A : F.Carrier → ℂ := fun a => ∫ u,
      signedWeylOrbitFourierKernel ψ ν m (U x) Φ (u, a)
        ∂unipotentHaar F.Carrier (m + 1)
    let B : F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier → ℂ := fun z => ∫ u,
      signedBlockOrbitKernel ψ m (U x) Φ (u, z)
        ∂unipotentHaar F.Carrier (m + 1)
    obtain ⟨_, hb, he⟩ := signedWeylOrbit_blockOrbit_fourier_duality_averaged
      F ψ ν hsd m (U x) (hunit x hx) Φ
    exact (integral_generalLinear_one_natWeight F ν A).trans
      ((congrArg (fun t : ℂ =>
        ((GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) : ℂ)⁻¹ * t)
        (he.trans (integral_prod B hb).symm)).trans
          (integral_generalLinear_one_prod_natWeight F (rectangularMeasure ν m 1) ν B).symm)

end Langlands.RankinSelberg
