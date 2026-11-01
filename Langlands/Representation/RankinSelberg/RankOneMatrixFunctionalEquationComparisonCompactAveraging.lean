import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonCornerAveraging

/-! Actual compact averaging of the unchanged Whittaker model vector. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.RankOneIwasawa

open MeasureTheory Topology GeneralLinear HarmonicAnalysis Whittaker

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance compactAvgTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance compactAvgValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance compactAvgLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance compactAvgT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance compactAvgTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance compactAvgSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance compactAvgMeasurable : MeasurableSpace F.Carrier := borel _
local instance compactAvgBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance compactAvgGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance compactAvgGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance compactAvgUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance compactAvgUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance compactAvgGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n F.Carrier) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F.Carrier))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F.Carrier)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology
local instance compactAvgUnitsSecondCountable : SecondCountableTopology F.Carrierˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance compactAvgMatrixLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Matrix (Fin n) (Fin n) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F.Carrier))
local instance compactAvgGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear n F.Carrier) := inferInstance
local instance compactAvgUnitsLocallyCompact : LocallyCompactSpace F.Carrierˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := F.Carrier)).locallyCompactSpace

/-- The actual outer Iwasawa measure in the tail and integral parameters. -/
def cornerParameterMeasure (n : ℕ) :
    Measure ((Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier) :=
  (tailMeasure F n).prod ((generalLinearHaar F.Carrier n).restrict (integralSet F n))

local instance compactAvgTailLocallyFinite (n : ℕ) : IsLocallyFiniteMeasure (tailMeasure F n) := by
  let : IsLocallyFiniteMeasure
      (Measure.pi fun _ : Fin n => localMultiplicativeHaar F.Carrier) := by
    exact @Measure.pi.isLocallyFiniteMeasure (Fin n) (fun _ => F.Carrierˣ) _ _
      (fun _ => localMultiplicativeHaar F.Carrier) _ _ (fun _ => inferInstance)
  unfold tailMeasure
  exact IsLocallyFiniteMeasure.withDensity_coe
    (μ := Measure.pi fun _ : Fin n => localMultiplicativeHaar F.Carrier)
    ((continuous_weight F n).comp (continuous_const.prodMk continuous_id))

instance cornerParameterMeasure_sigmaFinite (n : ℕ) : SigmaFinite (cornerParameterMeasure F n) := by
  unfold cornerParameterMeasure
  infer_instance

instance cornerParameterMeasure_finiteOnCompacts (n : ℕ) :
    IsFiniteMeasureOnCompacts (cornerParameterMeasure F n) := by
  unfold cornerParameterMeasure
  infer_instance

/-- The actual compact averaging parameter measure, using the supplied scalar Haar. -/
def cornerAveragingMeasure (n : ℕ) (ν : AdditiveHaarMeasure F.Carrier) :
    Measure (((Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier) ×
      F.Carrier) := (cornerParameterMeasure F n).prod ν.measure

instance cornerAveragingMeasure_finiteOnCompacts (n : ℕ) (ν : AdditiveHaarMeasure F.Carrier) :
    IsFiniteMeasureOnCompacts (cornerAveragingMeasure F n ν) := by
  unfold cornerAveragingMeasure
  infer_instance

/-- The fixed parameter map used for actual right averaging in positive rank. -/
def cornerAveragingTranslate (m : ℕ)
    (z : (((Fin (m + 1) → F.Carrierˣ) ×
      Langlands.GeneralLinear (m + 1 + 1) F.Carrier) × F.Carrier)) :
    Langlands.GeneralLinear (m + 1 + 1) F.Carrier :=
  rankOneCutoffUnipotent m z.2 * cornerAveragingPoint F z.1

theorem continuous_cornerAveragingTranslate (m : ℕ) :
    Continuous (cornerAveragingTranslate F m) :=
  ((continuous_transvectionUnit _ _ (rankOneCutoff_index_ne m)).comp continuous_snd).mul
    ((continuous_cornerAveragingPoint F (m + 1)).comp continuous_fst)

theorem rankOneEmbedding_mul_cornerAveragingPoint (m : ℕ)
    (g : Langlands.GeneralLinear (0 + 1) F.Carrier)
    (y : (Fin (m + 1) → F.Carrierˣ) × Langlands.GeneralLinear (m + 1 + 1) F.Carrier) :
    rankOneEmbedding m g * cornerAveragingPoint F y = diagPoint F (g, y) := by
  have hcoord : torusCoord (m + 1) (g, y.1) =
      Fin.cons (Matrix.GeneralLinearGroup.det g) 1 * torusCoord (m + 1) (1, y.1) := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp
  rw [cornerAveragingPoint, diagPoint, diagPoint, hcoord, map_mul, rankOneEmbedding, mul_assoc]

/-- The actual matrix identity introducing exactly the scalar corner phase. -/
theorem rankOneEmbedding_mul_cornerAveragingTranslate (m : ℕ)
    (g : Langlands.GeneralLinear (0 + 1) F.Carrier)
    (z : (((Fin (m + 1) → F.Carrierˣ) ×
      Langlands.GeneralLinear (m + 1 + 1) F.Carrier) × F.Carrier)) :
    rankOneEmbedding m g * cornerAveragingTranslate F m z =
      rankOneCutoffUnipotent m (((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) * z.2) *
        diagPoint F (g, z.1) := by
  rw [cornerAveragingTranslate, ← mul_assoc, rankOneEmbedding_mul_cutoffUnipotent,
    mul_assoc, rankOneEmbedding_mul_cornerAveragingPoint]

/-- On integral parameters every averaging translate has determinant norm one. -/
theorem abv_det_cornerAveragingTranslate (m : ℕ)
    (z : (((Fin (m + 1) → F.Carrierˣ) ×
      Langlands.GeneralLinear (m + 1 + 1) F.Carrier) × F.Carrier))
    (hz : z.1.2 ∈ integralSet F (m + 1)) :
    normalizedAbsoluteValue F.canonicalTopologicalData
      (Matrix.det (cornerAveragingTranslate F m z).val) = 1 := by
  rw [cornerAveragingTranslate, Units.val_mul,
    det_unipotent_mul F ⟨_, rankOneCutoffUnipotent_mem m z.2⟩]
  exact abv_det_cornerAveragingPoint F z.1 hz

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {m : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V)

/-- Standard Whittaker covariance for the unchanged input vector. -/
theorem glModelFunction_cornerAveragingTranslate
    (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (0 + 1) F.Carrier)
    (z : (((Fin (m + 1) → F.Carrierˣ) ×
      Langlands.GeneralLinear (m + 1 + 1) F.Carrier) × F.Carrier)) :
    glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g * cornerAveragingTranslate F m z) =
      ψ.complex (((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) * z.2) *
        glModelFunction ψ (m + 1) σ ℓ w (diagPoint F (g, z.1)) := by
  rw [rankOneEmbedding_mul_cornerAveragingTranslate]
  exact (glModelFunction_equivariance ψ (m + 1) σ ℓ w
    ⟨_, rankOneCutoffUnipotent_mem m _⟩ _).trans
      (by rw [standardCharacter_rankOneCutoffUnipotent])

/-- One universal compact kernel averages every input vector in its original
coefficient model. The scalar formula is obtained with genuine product
integrability and Fubini, using the unchanged supplied self-dual Haar measure. -/
theorem exists_compact_cornerAveragingModel
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ (m + 1) σ)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F.Carrier))
    (ν : AdditiveHaarMeasure F.Carrier) (hsd : IsSelfDual ψ ν) :
    ∃ K : SchwartzBruhat ((((Fin (m + 1) → F.Carrierˣ) ×
        Langlands.GeneralLinear (m + 1 + 1) F.Carrier) × F.Carrier)),
      ∀ w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
      ∃ w' : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
        (∀ h, Integrable (fun z => K z *
            glModelFunction ψ (m + 1) σ ℓ w (h * cornerAveragingTranslate F m z))
              (cornerAveragingMeasure F (m + 1) ν) ∧
          glModelFunction ψ (m + 1) σ ℓ w' h =
            ∫ z, K z * glModelFunction ψ (m + 1) σ ℓ w (h * cornerAveragingTranslate F m z)
              ∂(cornerAveragingMeasure F (m + 1) ν)) ∧
        ∀ g : Langlands.GeneralLinear (0 + 1) F.Carrier,
          Integrable (fun y => unipotentTransform F ψ Φ (diagPoint F (g, y)).val *
            glModelFunction ψ (m + 1) σ ℓ w (diagPoint F (g, y)))
              (cornerParameterMeasure F (m + 1)) ∧
          glModelFunction ψ (m + 1) σ ℓ w' (rankOneEmbedding m g) =
            ∫ y, unipotentTransform F ψ Φ (diagPoint F (g, y)).val *
              glModelFunction ψ (m + 1) σ ℓ w (diagPoint F (g, y))
                ∂(cornerParameterMeasure F (m + 1)) := by
  obtain ⟨R, E, K, hK, hrec⟩ := exists_cornerAveragingKernel F ψ Φ ν hsd
  refine ⟨K, fun w => ?_⟩
  obtain ⟨w', hw'⟩ := Smearing.exists_coefficient_average
    (cornerAveragingMeasure F (m + 1) ν) σ hσ ℓ (cornerAveragingTranslate F m)
    (continuous_cornerAveragingTranslate F m) K w
  refine ⟨w', hw', fun g => ?_⟩
  have hint := (hw' (rankOneEmbedding m g)).1
  have hinner : ∀ᵐ y ∂(cornerParameterMeasure F (m + 1)),
      (∫ v, K (y, v) * glModelFunction ψ (m + 1) σ ℓ w
        (rankOneEmbedding m g * cornerAveragingTranslate F m (y, v)) ∂ν.measure) =
        unipotentTransform F ψ Φ (diagPoint F (g, y)).val *
          glModelFunction ψ (m + 1) σ ℓ w (diagPoint F (g, y)) := by
    have hmem : ∀ᵐ y ∂(cornerParameterMeasure F (m + 1)),
        y.2 ∈ integralSet F (m + 1) := by
      exact Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem
        (show MeasurableSet (integralSet F (m + 1)) from
          (isCompact_integralSet F (m + 1)).measurableSet))
    filter_upwards [hmem] with y hy
    simp_rw [glModelFunction_cornerAveragingTranslate]
    calc
      _ = (∫ v, ψ.complex (((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) * v) *
          K (y, v) ∂ν.measure) * glModelFunction ψ (m + 1) σ ℓ w (diagPoint F (g, y)) := by
        rw [← integral_mul_const]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun v => by ring
      _ = _ := by rw [hrec g y hy]
  refine ⟨hint.integral_prod_left.congr hinner, ?_⟩
  change w'.val.val _ = _
  rw [(hw' (rankOneEmbedding m g)).2, cornerAveragingMeasure, integral_prod _ hint]
  exact integral_congr_ae hinner

end Langlands.RankinSelberg.RankOneIwasawa
