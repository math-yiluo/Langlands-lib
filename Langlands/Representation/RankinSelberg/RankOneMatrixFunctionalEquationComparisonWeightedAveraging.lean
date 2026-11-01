import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonCompactAveraging

/-! Weighted convergence for the actual compact model average. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.RankOneIwasawa

open MeasureTheory Topology GeneralLinear HarmonicAnalysis Whittaker

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance weightedAvgTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance weightedAvgValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance weightedAvgLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance weightedAvgT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance weightedAvgTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance weightedAvgSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance weightedAvgMeasurable : MeasurableSpace F.Carrier := borel _
local instance weightedAvgBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance weightedAvgGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance weightedAvgGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance weightedAvgUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance weightedAvgUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance weightedAvgGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n F.Carrier) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F.Carrier))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F.Carrier)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology
local instance weightedAvgUnitsSecondCountable : SecondCountableTopology F.Carrierˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance weightedAvgMatrixLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Matrix (Fin n) (Fin n) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F.Carrier))
local instance weightedAvgGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear n F.Carrier) := inferInstance
local instance weightedAvgUnitsLocallyCompact : LocallyCompactSpace F.Carrierˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := F.Carrier)).locallyCompactSpace

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {m : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V)

/-- An actual corner average inherits both convergence and the value of the
shifted matrix integral. This applies to the specific original-model average. -/
theorem rankOneModel_of_corner_average
    (ℓ : glFunctionals ψ (m + 1) σ)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F.Carrier))
    (w w' : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
    (havg : ∀ g : Langlands.GeneralLinear (0 + 1) F.Carrier,
      glModelFunction ψ (m + 1) σ ℓ w' (rankOneEmbedding m g) =
        ∫ y, unipotentTransform F ψ Φ (diagPoint F (g, y)).val *
          glModelFunction ψ (m + 1) σ ℓ w (diagPoint F (g, y))
            ∂(cornerParameterMeasure F (m + 1)))
    (s : ℂ)
    (hint : Integrable (GodementJacquet.matrixIntegrand abv Φ
      (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w))
        (generalLinearHaar F.Carrier (m + 1))) :
    Integrable (rankOneModelIntegrand ψ abv σ ℓ w' s) (generalLinearHaar F.Carrier 0) ∧
      ∫ h, GodementJacquet.matrixIntegrand abv Φ
          (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w) h
            ∂(generalLinearHaar F.Carrier (m + 1)) =
        ∫ g, rankOneModelIntegrand ψ abv σ ℓ w' s g ∂(generalLinearHaar F.Carrier 0) := by
  obtain ⟨hI, hEq⟩ := integral_matrixIntegrand_unfold F ψ Φ
    (glModelFunction ψ (m + 1) σ ℓ w)
    (fun u h => glModelFunction_equivariance ψ (m + 1) σ ℓ w u h)
    (s + GodementJacquet.jpssShift (m + 1)) hint
  have hae : (fun x => unipotentTransform F ψ Φ (diagPoint F x).val *
      (glModelFunction ψ (m + 1) σ ℓ w (diagPoint F x) *
        determinantWeight abv (diagPoint F x) (s + GodementJacquet.jpssShift (m + 1))))
      =ᵐ[outerMeasure F (m + 1)]
        (fun x => (unipotentTransform F ψ Φ (diagPoint F x).val *
          glModelFunction ψ (m + 1) σ ℓ w (diagPoint F x)) *
            determinantWeight abv x.1 (s + GodementJacquet.jpssShift (m + 1))) := by
    filter_upwards [ae_outerMeasure_mem F] with x hx
    rw [determinantWeight_diagPoint F _ x hx, mul_assoc]
  have hIprod : Integrable (fun x =>
      (unipotentTransform F ψ Φ (diagPoint F x).val *
        glModelFunction ψ (m + 1) σ ℓ w (diagPoint F x)) *
          determinantWeight abv x.1 (s + GodementJacquet.jpssShift (m + 1)))
      ((glOneMeasure F (m + 1)).prod (cornerParameterMeasure F (m + 1))) := hI.congr hae
  have hpoint : ∀ g : Langlands.GeneralLinear (0 + 1) F.Carrier,
      (∫ y, (unipotentTransform F ψ Φ (diagPoint F (g, y)).val *
          glModelFunction ψ (m + 1) σ ℓ w (diagPoint F (g, y))) *
            determinantWeight abv g (s + GodementJacquet.jpssShift (m + 1))
              ∂(cornerParameterMeasure F (m + 1))) =
        glModelFunction ψ (m + 1) σ ℓ w' (rankOneEmbedding m g) *
          determinantWeight abv g (s + GodementJacquet.jpssShift (m + 1)) := by
    intro g
    rw [integral_mul_const, havg g]
  have hwm : Measurable fun g : Langlands.GeneralLinear (0 + 1) F.Carrier =>
      weight F (m + 1) (g, 1) :=
    (continuous_weight F (m + 1)).measurable.comp (measurable_id.prodMk measurable_const)
  have hpt : ∀ g : Langlands.GeneralLinear (0 + 1) F.Carrier,
      weight F (m + 1) (g, 1) •
        (glModelFunction ψ (m + 1) σ ℓ w' (rankOneEmbedding m g) *
          determinantWeight abv g (s + GodementJacquet.jpssShift (m + 1))) =
        rankOneModelIntegrand ψ abv σ ℓ w' s g := by
    intro g
    exact weight_smul_determinantWeight F g s _
  have hres := hIprod.integral_prod_left.congr (Filter.Eventually.of_forall hpoint)
  rw [glOneMeasure, integrable_withDensity_iff_integrable_smul hwm] at hres
  refine ⟨hres.congr (Filter.Eventually.of_forall hpt), ?_⟩
  rw [hEq, integral_congr_ae hae]
  change (∫ x, _ ∂((glOneMeasure F (m + 1)).prod
    (cornerParameterMeasure F (m + 1)))) = _
  rw [integral_prod _ hIprod, integral_congr_ae (Filter.Eventually.of_forall hpoint),
    glOneMeasure, integral_withDensity_eq_integral_smul hwm]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- The universal compact kernel yields one original-model vector, independent
of the spectral parameter, whose rank-one integral agrees with the matrix one
wherever the latter is absolutely convergent. -/
theorem exists_weighted_compact_cornerAveragingModel
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
        (∀ g : Langlands.GeneralLinear (0 + 1) F.Carrier,
          glModelFunction ψ (m + 1) σ ℓ w' (rankOneEmbedding m g) =
            ∫ y, unipotentTransform F ψ Φ (diagPoint F (g, y)).val *
              glModelFunction ψ (m + 1) σ ℓ w (diagPoint F (g, y))
                ∂(cornerParameterMeasure F (m + 1))) ∧
        ∀ s : ℂ,
          Integrable (GodementJacquet.matrixIntegrand abv Φ
            (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w))
              (generalLinearHaar F.Carrier (m + 1)) →
          Integrable (rankOneModelIntegrand ψ abv σ ℓ w' s) (generalLinearHaar F.Carrier 0) ∧
            ∫ h, GodementJacquet.matrixIntegrand abv Φ
                (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w) h
                  ∂(generalLinearHaar F.Carrier (m + 1)) =
              ∫ g, rankOneModelIntegrand ψ abv σ ℓ w' s g ∂(generalLinearHaar F.Carrier 0) := by
  obtain ⟨K, hK⟩ := exists_compact_cornerAveragingModel F ψ σ hσ ℓ Φ ν hsd
  refine ⟨K, fun w => ?_⟩
  obtain ⟨w', havg, hres⟩ := hK w
  refine ⟨w', havg, fun g => (hres g).2, fun s hint => ?_⟩
  exact rankOneModel_of_corner_average F ψ σ ℓ Φ w w' (fun g => (hres g).2) s hint

/-- Choose the actual compact original-model average with one kernel fixed before
all input vectors, and with its convergence valid for every spectral parameter. -/
def weightedCornerAverage (hσ : IsSmooth σ) (ℓ : glFunctionals ψ (m + 1) σ)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F.Carrier))
    (ν : AdditiveHaarMeasure F.Carrier) (hsd : IsSelfDual ψ ν)
    (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule) :
    (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule :=
  Classical.choose ((Classical.choose_spec
    (exists_weighted_compact_cornerAveragingModel F ψ σ hσ ℓ Φ ν hsd)) w)

/-- The selected original-model average has the actual weighted matrix comparison. -/
theorem weightedCornerAverage_comparison (hσ : IsSmooth σ)
    (ℓ : glFunctionals ψ (m + 1) σ)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F.Carrier))
    (ν : AdditiveHaarMeasure F.Carrier) (hsd : IsSelfDual ψ ν)
    (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule) (s : ℂ)
    (hint : Integrable (GodementJacquet.matrixIntegrand abv Φ
      (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w))
        (generalLinearHaar F.Carrier (m + 1))) :
    Integrable (rankOneModelIntegrand ψ abv σ ℓ
      (weightedCornerAverage F ψ σ hσ ℓ Φ ν hsd w) s) (generalLinearHaar F.Carrier 0) ∧
      ∫ h, GodementJacquet.matrixIntegrand abv Φ
          (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w) h
            ∂(generalLinearHaar F.Carrier (m + 1)) =
        ∫ g, rankOneModelIntegrand ψ abv σ ℓ
          (weightedCornerAverage F ψ σ hσ ℓ Φ ν hsd w) s g ∂(generalLinearHaar F.Carrier 0) := by
  exact (Classical.choose_spec ((Classical.choose_spec
    (exists_weighted_compact_cornerAveragingModel F ψ σ hσ ℓ Φ ν hsd)) w)).2.2 s hint

end Langlands.RankinSelberg.RankOneIwasawa
