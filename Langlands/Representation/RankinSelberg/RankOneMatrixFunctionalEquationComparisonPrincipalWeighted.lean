import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalAverage

/-! # Spectral weights in principal compact-measure extraction -/

noncomputable section

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace Langlands.RankinSelberg.RankOneBox

open GeneralLinear HarmonicAnalysis Whittaker Conductor RankOneIwasawa

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance principalWeightedTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance principalWeightedValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance principalWeightedLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance principalWeightedT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance principalWeightedGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance principalWeightedGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable {n : ℕ}

/-- A right factor with determinant norm one does not change any spectral
determinant weight. -/
theorem determinantWeight_mul_of_norm_one
    (g k : Langlands.GeneralLinear (n + 1) F.Carrier)
    (hk : abv (Matrix.det k.val) = 1) (s : ℂ) :
    determinantWeight abv (g * k) s = determinantWeight abv g s := by
  simp only [determinantWeight, Units.val_mul, Matrix.det_mul, map_mul, hk, mul_one]

/-- The scalar embedding preserves the actual determinant weight. -/
theorem determinantWeight_rankOneEmbedding (m : ℕ)
    (g : Langlands.GeneralLinear (0 + 1) F.Carrier) (s : ℂ) :
    determinantWeight abv (rankOneEmbedding m g) s = determinantWeight abv g s := by
  have hd : Matrix.GeneralLinearGroup.det (rankOneEmbedding m g) =
      Matrix.GeneralLinearGroup.det g := by
    simp [rankOneEmbedding, det_diagonalUnits, Fin.prod_univ_succ]
  unfold determinantWeight
  exact congrArg (fun x : F.Carrierˣ => ((abv (x : F.Carrier) : ℝ) : ℂ) ^ s) hd

/-- Spectral multiplication preserves the standard left character. -/
theorem determinantWeighted_equivariant
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (heq : ∀ u : upperUnipotent (n + 1) F.Carrier, ∀ h,
      W (u.val * h) = (standardCharacter ψ n u : ℂ) * W h)
    (s : ℂ) (u : upperUnipotent (n + 1) F.Carrier) (g) :
    W (u.val * g) * determinantWeight abv (u.val * g) s =
      (standardCharacter ψ n u : ℂ) * (W g * determinantWeight abv g s) := by
  have hd : determinantWeight abv (u.val * g) s = determinantWeight abv g s := by
    unfold determinantWeight
    rw [Units.val_mul, det_unipotent_mul]
  rw [heq, hd, mul_assoc]

/-- The same compact principal measure factors out every spectral weight.
The identity uses its actual determinant-norm-one support. -/
theorem principalAveragingMeasure_weighted_integral (a : ℕ) (C : ℝ)
    (W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) (s : ℂ) :
    ∫ k, W (g * k) * determinantWeight abv (g * k) s
        ∂principalAveragingMeasure F a C =
      (∫ k, W (g * k) ∂principalAveragingMeasure F a C) *
        determinantWeight abv g s := by
  calc
    _ = ∫ k, W (g * k) * determinantWeight abv g s
        ∂principalAveragingMeasure F a C := by
      apply integral_congr_ae
      filter_upwards [principalAveragingMeasure_ae_det_norm F a C] with k hk
      rw [determinantWeight_mul_of_norm_one F g k hk]
    _ = _ := integral_mul_const _ _

/-- The scalar restriction of a model function after the fixed principal
compact average, with its spectral determinant weight. -/
def principalWeightedScalarAverage {m : ℕ} (a : ℕ) (C : ℝ)
    (W : Langlands.GeneralLinear (m + 1 + 1) F.Carrier → ℂ) (s : ℂ)
    (g : Langlands.GeneralLinear (0 + 1) F.Carrier) : ℂ :=
  (∫ k, W (rankOneEmbedding m g * k) ∂principalAveragingMeasure F a C) *
    determinantWeight abv g s

/-- Universal original extraction at every complex spectral parameter, with
one test, one compact measure, and genuine convergence of the scalar average. -/
theorem principalMeasure_weighted_extraction (ψ : UnitaryAdditiveCharacter F.Carrier)
    {m : ℕ} {a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ F.canonicalTopologicalData.additiveConductor ψ + a)
    (W : Langlands.GeneralLinear (m + 1 + 1) F.Carrier → ℂ) (hW : Continuous W)
    (heq : ∀ u : upperUnipotent (m + 1 + 1) F.Carrier, ∀ h,
      W (u.val * h) = (standardCharacter ψ (m + 1) u : ℂ) * W h)
    (s : ℂ)
    (hconv : Integrable (GodementJacquet.matrixIntegrand abv
      (boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a) s W)
      (generalLinearHaar F.Carrier (m + 1))) :
    let C := boxExtractionConstant F (n := m + 1)
      (F.canonicalTopologicalData.additiveConductor ψ + a)
      (F.canonicalTopologicalData.additiveConductor ψ) a
    Integrable (principalWeightedScalarAverage F a C W s)
      (glOneMeasure F (m + 1)) ∧
    GodementJacquet.matrixIntegral abv (generalLinearHaar F.Carrier (m + 1))
      (boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a) s W =
      ∫ g, principalWeightedScalarAverage F a C W s g
        ∂glOneMeasure F (m + 1) := by
  dsimp only [principalWeightedScalarAverage]
  have hc : Integrable (fun h =>
      boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a h.val *
          (W h * determinantWeight abv h s))
      (generalLinearHaar F.Carrier (m + 1)) := by
    change Integrable (fun h =>
      boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a h.val * W h *
          determinantWeight abv h s) (generalLinearHaar F.Carrier (m + 1)) at hconv
    simpa only [mul_assoc] using hconv
  obtain ⟨hi, hv⟩ := principalMeasure_extraction F ψ ha hA
    (fun h => W h * determinantWeight abv h s)
    (hW.mul (continuous_determinantWeight F _ s))
    (determinantWeighted_equivariant F ψ W heq s) hc
  simp_rw [principalAveragingMeasure_weighted_integral,
    determinantWeight_rankOneEmbedding] at hi hv
  refine ⟨hi, ?_⟩
  simpa only [GodementJacquet.matrixIntegral, GodementJacquet.matrixIntegrand,
    mul_assoc] using hv

end Langlands.RankinSelberg.RankOneBox
