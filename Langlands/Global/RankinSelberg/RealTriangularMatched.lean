import Langlands.Global.RankinSelberg.RealTriangularWeights
import Langlands.Global.RankinSelberg.RealTriangularInversion
import Langlands.Global.RankinSelberg.RealGodementFourierCovariance

/-! # Matched triangular expansions with a function of the absolute determinant -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.Global.RankinSelbergGlobal.RealSquareFourier
open Langlands.Global.RankinSelbergGlobal.RealGodement
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean

variable {n : ℕ}
local notation "I" => Fin n
local notation "M" => Matrix I I ℝ
local notation "G" => GeneralLinear n ℝ
local notation "D" => I → ℝˣ
local notation "J" => UpperEntryPair n
local notation "U" => upperUnipotent n ℝ
local notation "Kc" => unitaryCompact ℝ n

local instance realMatchedMatrixSecondCountable : SecondCountableTopology M :=
  inferInstanceAs (SecondCountableTopology (I → I → ℝ))
local instance realMatchedGLSecondCountable : SecondCountableTopology G :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology
local instance realMatchedGLMeasurable : MeasurableSpace G := borel _
local instance realMatchedGLBorel : BorelSpace G := ⟨rfl⟩
local instance realMatchedUnitsMeasurable : MeasurableSpace ℝˣ := borel _
local instance realMatchedUnitsBorel : BorelSpace ℝˣ := ⟨rfl⟩
local instance realMatchedDiagonalSigmaFinite : SigmaFinite (realDiagonalHaar n) := by
  unfold realDiagonalHaar
  infer_instance
local instance realMatchedSelfDualHaar (b : ℝˣ) : (realSelfDualMeasure b).measure.IsAddHaarMeasure :=
  (realSelfDualMeasure b).isAddHaar

theorem matrixTransform_eq_realRectangularSchwartzFourier (b : ℝˣ) (Φ : 𝓢(M, ℂ)) (X : M) :
    matrixTransform b Φ X = realRectangularSchwartzFourier b Φ X := by
  rw [matrixTransform_apply, realRectangularSchwartzFourier_apply]
  unfold rectangularFourierIntegral RankinSelberg.rectangularMeasure
  apply integral_congr_ae
  refine ae_of_all _ fun Y => ?_
  let Y' : M := Y
  have h : Matrix.trace (Xᵀ * Y') = rectangularPairing Y' X := by
    change (∑ i : I, ∑ j : I, X j i * Y' j i) = ∑ i : I, ∑ j : I, Y' i j * X i j
    rw [Finset.sum_comm]
    simp only [mul_comm]
  change Φ Y' * (realScaledCharacter b).complex (Matrix.trace (Xᵀ * Y')) =
    Φ Y' * (realScaledCharacter b).complex (rectangularPairing Y' X)
  rw [h]

/-- Left-right covariance of the square transform, in the measure of the same character. -/
theorem matrixTransform_translate (b : ℝˣ) (A B : G) (Φ : 𝓢(M, ℂ)) (X : M) :
    matrixTransform b (rectangularTranslate A B Φ) X =
      (((|A.val.det| ^ n * |B.val.det| ^ n)⁻¹ : ℝ) : ℂ) *
        matrixTransform b Φ ((inverseTranspose n ℝ A).val * X * (inverseTranspose n ℝ B).val) := by
  simp only [matrixTransform_eq_realRectangularSchwartzFourier]
  exact realGodementFourierCovariance n n b A B Φ X

/-- Diagonal Schwartz test attached to the compact right translate of the square test. -/
def realTriangularMarginal (b : ℝˣ) (Φ : 𝓢(M, ℂ)) (k : Kc) : 𝓢(I → ℝ, ℂ) :=
  upperMarginal b (rectangularTranslate 1 k.val Φ)

theorem realTriangularMarginal_apply (b : ℝˣ) (Φ : 𝓢(M, ℂ)) (k : Kc) (d : I → ℝ) :
    realTriangularMarginal b Φ k d = ∫ X : J → ℝ, Φ (upperTriangularEntries d X * k.val.val)
      ∂upperEntryProductMeasure (realSelfDualMeasure b) n := by
  simp only [realTriangularMarginal, upperMarginal_apply, rectangularTranslate_apply,
    Units.val_one, Matrix.one_mul, upperEntryProductMeasure]

theorem integral_realLowerMatrixTransform (b : ℝˣ) (Φ : 𝓢(M, ℂ)) (k : Kc) (d : I → ℝ) :
    (∫ X : J → ℝ, matrixTransform b Φ ((upperTriangularEntries d X)ᵀ * k.val.val)
      ∂upperEntryProductMeasure (realSelfDualMeasure b) n) =
      realFourierTransform b (realTriangularMarginal b Φ k) d := by
  have hcov (Y : M) : matrixTransform b (rectangularTranslate 1 k.val Φ) Y =
      matrixTransform b Φ (Y * k.val.val) := by
    rw [matrixTransform_translate, realInverseTranspose_unitary_eq, map_one, Units.val_one,
      Matrix.det_one, abs_one, one_pow, Matrix.one_mul,
      RealJacquetCoefficient.abs_det_eq_one_of_mem k.property]
    simp
  simp_rw [← hcov]
  exact realSquareFourierMarginal b (rectangularTranslate 1 k.val Φ) d

private def triangularPoint (d : D) (X : J → ℝ) (k : Kc) : G :=
  diagonalMatrixUnits ℝ d * ((upperEntryCoordinates n).symm X).val * k.val

private theorem continuous_triangularPoint :
    Continuous (fun p : (D × (J → ℝ)) × Kc => triangularPoint p.1.1 p.1.2 p.2) := by
  have hD : Continuous (diagonalMatrixUnits ℝ : D → G) := by
    apply Units.continuous_iff.2
    have h : Continuous (fun d : D => (diagonalMatrixUnits ℝ d).val) :=
      (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i)).matrix_diagonal
    exact ⟨h, by simpa only [Function.comp_def, map_inv] using h.comp continuous_inv⟩
  exact ((hD.comp (continuous_fst.comp continuous_fst)).mul
    (continuous_subtype_val.comp ((upperEntryCoordinates n).symm.continuous.comp
      (continuous_snd.comp continuous_fst)))).mul (continuous_subtype_val.comp continuous_snd)

/-- The full real triangular Haar formula with the entry variable integrated first.
The two remaining variables give an integrable function on the compact-diagonal product. -/
theorem exists_realHaar_integral_triangular (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (ν : AdditiveHaarMeasure ℝ) [SigmaFinite ν.measure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ F : G → ℂ, Measurable F → Integrable F μ →
      let A (p : Kc × D) := ∫ X, F (triangularPoint p.2 X p.1) ∂upperEntryProductMeasure ν n
      Integrable A (κ.prod (realDiagonalHaar n)) ∧
        (∫ g, F g ∂μ) = (c : ℂ) * ∫ p, A p ∂(κ.prod (realDiagonalHaar n)) := by
  let δ := realDiagonalHaar n
  let υ := upperEntryProductMeasure ν n
  let H (p : (D × (J → ℝ)) × Kc) := triangularPoint p.1.1 p.1.2 p.2
  have hH : Measurable H := (continuous_triangularPoint (n := n)).measurable
  obtain ⟨c, hc, hμ⟩ := realTriangularHaar n μ ν κ inferInstance inferInstance
  change μ = c • (((δ.prod υ).prod κ).map H) at hμ
  let e₁ : ((Kc × D) × (J → ℝ)) ≃ᵐ Kc × D × (J → ℝ) := MeasurableEquiv.prodAssoc
  let e₂ : (Kc × D × (J → ℝ)) ≃ᵐ (D × (J → ℝ)) × Kc := MeasurableEquiv.prodComm
  let e := e₁.trans e₂
  have he : MeasurePreserving e ((κ.prod δ).prod υ) ((δ.prod υ).prod κ) :=
    (measurePreserving_swap (μ := κ) (ν := δ.prod υ)).comp (measurePreserving_prodAssoc κ δ υ)
  refine ⟨c, hc, fun F hF hInt => ?_⟩
  rw [hμ] at hInt
  have hmap : Integrable F (((δ.prod υ).prod κ).map H) :=
    (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hc.ne') ENNReal.coe_ne_top).mp hInt
  have hInt' : Integrable (F ∘ H) ((δ.prod υ).prod κ) := hmap.comp_measurable hH
  have hInt'' : Integrable (F ∘ H ∘ e) ((κ.prod δ).prod υ) := he.integrable_comp_of_integrable hInt'
  refine ⟨hInt''.integral_prod_left, ?_⟩
  rw [hμ, integral_smul_nnreal_measure, integral_map hH.aemeasurable hF.aestronglyMeasurable]
  simp only [NNReal.smul_def, Complex.real_smul]
  change (c : ℂ) * (∫ p, (F ∘ H) p ∂((δ.prod υ).prod κ)) = _
  rw [← he.integral_comp' (F ∘ H)]
  exact congrArg ((c : ℂ) * ·) (integral_prod (F ∘ H ∘ e) hInt'')

variable {r : ℕ}
local notation "n₁" => r + 1

/-- Matrix integrand with the normalized rank shift and an independent determinant function. -/
def realMatrixWeightedIntegrand (f : GeneralLinear n₁ ℝ → ℂ)
    (Φ : Matrix (Fin n₁) (Fin n₁) ℝ → ℂ) (h : ℝ → ℂ) (g : GeneralLinear n₁ ℝ) : ℂ :=
  Φ g.val * f g * detPower realNormalizedAbs g ((r : ℂ) / 2) * h (realNormalizedAbs g.val.det)

theorem measurable_realMatrixWeightedIntegrand {f : GeneralLinear n₁ ℝ → ℂ} (hf : Continuous f)
    {Φ : Matrix (Fin n₁) (Fin n₁) ℝ → ℂ} (hΦ : Continuous Φ) {h : ℝ → ℂ} (hh : Measurable h) :
    Measurable (realMatrixWeightedIntegrand f Φ h) := by
  have hd : Measurable (fun g : GeneralLinear n₁ ℝ => realNormalizedAbs g.val.det) :=
    (continuous_abs.comp Units.continuous_val.matrix_det).measurable
  exact (((hΦ.measurable.comp Units.continuous_val.measurable).mul hf.measurable).mul
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (Real.measurable_log.comp hd))))).mul (hh.comp hd)

/-- The diagonal integrand after the entry Jacobian and half-modulus cancel the rank shift. -/
def realDiagonalWeightedIntegrand (χ : ℕ → ℝˣ → ℂ) (v : ℂ) (Φ : (Fin n₁ → ℝ) → ℂ)
    (h : ℝ → ℂ) (d : Fin n₁ → ℝˣ) : ℂ :=
  realDiagonalZetaWeight χ d 0 * v * Φ (fun i => (d i : ℝ)) * h (realDiagonalAbs d)

private theorem integral_realMatrixWeighted_primal (b : ℝˣ)
    {χ : ℕ → ℝˣ → ℂ} {f : GeneralLinear n₁ ℝ → ℂ} (hf : f ∈ principalSeries ℝ n₁ χ)
    (Φ : 𝓢(Matrix (Fin n₁) (Fin n₁) ℝ, ℂ)) (h : ℝ → ℂ)
    (d : Fin n₁ → ℝˣ) (k : unitaryCompact ℝ n₁) :
    (∫ X, realMatrixWeightedIntegrand f Φ h (triangularPoint d X k)
      ∂upperEntryProductMeasure (realSelfDualMeasure b) n₁) =
      realDiagonalWeightedIntegrand χ (f k.val) (realTriangularMarginal b Φ k) h d := by
  let ν := realSelfDualMeasure b
  let A := principalSeriesCharacter ℝ n₁ χ d
  let t := detPower realNormalizedAbs (diagonalMatrixUnits ℝ d * (1 : upperUnipotent n₁ ℝ).val * k.val)
    ((r : ℂ) / 2)
  let F (Y : Matrix (Fin n₁) (Fin n₁) ℝ) := Φ (Y * k.val.val)
  have hF : Continuous F := Φ.continuous.comp (continuous_id.matrix_mul continuous_const)
  have hpoint (X : UpperEntryPair n₁ → ℝ) :
      realMatrixWeightedIntegrand f Φ h (triangularPoint d X k) =
        F ((diagonalMatrixUnits ℝ d).val * ((upperEntryCoordinates n₁).symm X).val.val) *
          (A * f k.val) * t * h (realDiagonalAbs d) := by
    have hf' := hf.2 d ((upperEntryCoordinates n₁).symm X) k.val
    change f (triangularPoint d X k) = A * f k.val at hf'
    rw [realMatrixWeightedIntegrand, hf', triangularPoint, realNormalizedAbs_det_triangular]
    simp only [F, t, Units.val_mul, detPower_real_triangular]
  simp_rw [hpoint, integral_mul_const]
  rw [integral_realDiagonal_mul_upperEntries ν d F hF]
  have hW := realTriangular_zetaWeight χ d (1 : upperUnipotent n₁ ℝ) k 0
  rw [zero_add] at hW
  let c : ℂ := ((↑((∏ ij : UpperEntryPair n₁, ‖(d ij.1.1 : ℝ)‖₊)⁻¹) : ℝ) : ℂ)
  let B := realTriangularMarginal b Φ k (fun i => (d i : ℝ))
  change ((c * ∫ X, F (upperTriangularEntries (fun i => (d i : ℝ)) X)
    ∂upperEntryProductMeasure ν n₁) * (A * f k.val) * t * h (realDiagonalAbs d)) = _
  rw [← realTriangularMarginal_apply b Φ k]
  change (c * B) * (A * f k.val) * t * h (realDiagonalAbs d) =
    realDiagonalZetaWeight χ d 0 * f k.val * B * h (realDiagonalAbs d)
  calc
    _ = (c * A * t) * f k.val * B * h (realDiagonalAbs d) := by ring
    _ = _ := by rw [show c * A * t = realDiagonalZetaWeight χ d 0 from hW]

private theorem integral_realMatrixWeighted_dual (b : ℝˣ)
    {χ : ℕ → ℝˣ → ℂ} {f : GeneralLinear n₁ ℝ → ℂ} (hf : f ∈ principalSeries ℝ n₁ χ)
    (Φ : 𝓢(Matrix (Fin n₁) (Fin n₁) ℝ, ℂ)) (h : ℝ → ℂ)
    (d : Fin n₁ → ℝˣ) (k : unitaryCompact ℝ n₁) :
    let ι := inverseTranspose n₁ ℝ
    (∫ X, realMatrixWeightedIntegrand (f ∘ ι) (matrixTransform b Φ) h (ι (triangularPoint d⁻¹ X k))
      ∂upperEntryProductMeasure (realSelfDualMeasure b) n₁) =
      realDiagonalWeightedIntegrand (fun i z => χ i z⁻¹) (f k.val)
        (realFourierTransform b (realTriangularMarginal b Φ k)) h d := by
  let ι := inverseTranspose n₁ ℝ
  let ν := realSelfDualMeasure b
  let e := (upperEntryCoordinates n₁ (K := ℝ)).symm.toMeasurableEquiv
  let μU := (upperEntryProductMeasure ν n₁).map e
  let A := principalSeriesCharacter ℝ n₁ χ d⁻¹
  let t := detPower realNormalizedAbs (ι (diagonalMatrixUnits ℝ d⁻¹ * (1 : upperUnipotent n₁ ℝ).val *
    k.val)) ((r : ℂ) / 2)
  let F (Y : Matrix (Fin n₁) (Fin n₁) ℝ) := matrixTransform b Φ (Yᵀ * k.val.val)
  have hF : Continuous F := (matrixTransform b Φ).continuous.comp
    (continuous_id.matrix_transpose.matrix_mul continuous_const)
  let H (u : upperUnipotent n₁ ℝ) := realMatrixWeightedIntegrand (f ∘ ι) (matrixTransform b Φ) h
    (ι (diagonalMatrixUnits ℝ d⁻¹ * u.val * k.val))
  have hinv : MeasurePreserving (Inv.inv : upperUnipotent n₁ ℝ → upperUnipotent n₁ ℝ) μU μU :=
    realUpperEntryProductMeasure_measurePreserving_inv n₁ ν
  change (∫ X, H (e X) ∂upperEntryProductMeasure ν n₁) = _
  rw [← e.measurableEmbedding.integral_map, ← hinv.integral_comp (MeasurableEquiv.inv _).measurableEmbedding H]
  change (∫ u, H u⁻¹ ∂(upperEntryProductMeasure ν n₁).map e) = _
  rw [e.measurableEmbedding.integral_map]
  have hpoint (u : upperUnipotent n₁ ℝ) : H u⁻¹ =
      F (u.val.val * (diagonalMatrixUnits ℝ d).val) * (A * f k.val) * t * h (realDiagonalAbs d) := by
    rw [show H u⁻¹ = matrixTransform b Φ (ι (diagonalMatrixUnits ℝ d⁻¹ * (u⁻¹).val * k.val)).val *
        f (ι (ι (diagonalMatrixUnits ℝ d⁻¹ * (u⁻¹).val * k.val))) *
        detPower realNormalizedAbs (ι (diagonalMatrixUnits ℝ d⁻¹ * (u⁻¹).val * k.val)) ((r : ℂ) / 2) *
        h (realNormalizedAbs (ι (diagonalMatrixUnits ℝ d⁻¹ * (u⁻¹).val * k.val)).val.det) from rfl]
    rw [show ∀ g, ι (ι g) = g from inverseTranspose_involutive n₁ ℝ,
      realNormalizedAbs_det_dualTriangular, realInverseTranspose_triangularPoint]
    have hf' : f (diagonalMatrixUnits ℝ d⁻¹ * (u⁻¹).val * k.val) = A * f k.val := hf.2 d⁻¹ u⁻¹ k.val
    rw [hf']
    simp only [F, t, ι, detPower_real_dualTriangular]
  simp_rw [hpoint, integral_mul_const]
  change (∫ X, F (((upperEntryCoordinates n₁).symm X).val.val * (diagonalMatrixUnits ℝ d).val)
    ∂upperEntryProductMeasure ν n₁) * (A * f k.val) * t * h (realDiagonalAbs d) = _
  rw [integral_realUpperEntries_mul_diagonal ν d F hF]
  have hW := realTriangular_dualZetaWeight χ d (1 : upperUnipotent n₁ ℝ) k 0
  rw [zero_add] at hW
  let c : ℂ := ((↑((∏ ij : UpperEntryPair n₁, ‖(d ij.1.2 : ℝ)‖₊)⁻¹) : ℝ) : ℂ)
  let B := realFourierTransform b (realTriangularMarginal b Φ k) (fun i => (d i : ℝ))
  change ((c * ∫ X, F (upperTriangularEntries (fun i => (d i : ℝ)) X)
    ∂upperEntryProductMeasure ν n₁) * (A * f k.val) * t * h (realDiagonalAbs d)) = _
  rw [integral_realLowerMatrixTransform b Φ k (fun i => (d i : ℝ))]
  change (c * B) * (A * f k.val) * t * h (realDiagonalAbs d) =
    realDiagonalZetaWeight (fun i z => χ i z⁻¹) d 0 * f k.val * B * h (realDiagonalAbs d)
  calc
    _ = (c * A * t) * f k.val * B * h (realDiagonalAbs d) := by ring
    _ = _ := by rw [show c * A * t = realDiagonalZetaWeight (fun i z => χ i z⁻¹) d 0 from hW]

/-- Primal and dual weighted integrals have a common Haar constant and matched diagonal tests. -/
def RealTriangularMatchedStatement : Prop :=
  ∀ (μ : Measure (GeneralLinear n₁ ℝ)) (κ : Measure (unitaryCompact ℝ n₁)) (b : ℝˣ),
    ∀ [μ.IsHaarMeasure] [κ.IsHaarMeasure] [SFinite κ],
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (χ : ℕ → ℝˣ → ℂ) (f : GeneralLinear n₁ ℝ → ℂ),
      f ∈ principalSeries ℝ n₁ χ → ∀ (Φ : 𝓢(Matrix (Fin n₁) (Fin n₁) ℝ, ℂ))
        (h : ℝ → ℂ), Measurable h →
      let η := κ.prod (realDiagonalHaar n₁)
      let ι := inverseTranspose n₁ ℝ
      let P := realMatrixWeightedIntegrand f Φ h
      let Q := realMatrixWeightedIntegrand (f ∘ ι) (matrixTransform b Φ) h
      let A (p : unitaryCompact ℝ n₁ × (Fin n₁ → ℝˣ)) :=
        realDiagonalWeightedIntegrand χ (f p.1.val) (realTriangularMarginal b Φ p.1) h p.2
      let B (p : unitaryCompact ℝ n₁ × (Fin n₁ → ℝˣ)) :=
        realDiagonalWeightedIntegrand (fun i z => χ i z⁻¹) (f p.1.val)
          (realFourierTransform b (realTriangularMarginal b Φ p.1)) h p.2
      (Integrable P μ → Integrable A η ∧ (∫ g, P g ∂μ) = (c : ℂ) * ∫ p, A p ∂η) ∧
      (Integrable Q μ → Integrable B η ∧ (∫ g, Q g ∂μ) = (c : ℂ) * ∫ p, B p ∂η)

theorem realTriangularMatched : RealTriangularMatchedStatement (r := r) := by
  intro μ κ b hμ hκ hκs
  let ν := realSelfDualMeasure b
  let η := κ.prod (realDiagonalHaar n₁)
  let ι := inverseTranspose n₁ ℝ
  obtain ⟨c, hc, hcF⟩ := exists_realHaar_integral_triangular μ κ ν
  refine ⟨c, hc, fun χ f hf Φ h hh => ?_⟩
  have hfc : Continuous f := hf.1.continuous
  constructor
  · intro hP
    have hm := measurable_realMatrixWeightedIntegrand hfc Φ.continuous hh
    obtain ⟨hA, hEq⟩ := hcF _ hm hP
    have hmatch : (fun p : unitaryCompact ℝ n₁ × (Fin n₁ → ℝˣ) =>
        ∫ X, realMatrixWeightedIntegrand f Φ h (triangularPoint p.2 X p.1)
          ∂upperEntryProductMeasure ν n₁) =
        fun p => realDiagonalWeightedIntegrand χ (f p.1.val) (realTriangularMarginal b Φ p.1) h p.2 :=
      funext fun p => integral_realMatrixWeighted_primal b hf Φ h p.2 p.1
    rw [hmatch] at hA hEq
    exact ⟨hA, hEq⟩
  · intro hQ
    let Q := realMatrixWeightedIntegrand (f ∘ ι) (matrixTransform b Φ) h
    let e := (inverseTransposeContinuous n₁ ℝ).toHomeomorph.toMeasurableEquiv
    have he : MeasurePreserving e μ μ := realHaar_measurePreserving_inverseTranspose n₁ μ
    have hm := measurable_realMatrixWeightedIntegrand
      (hfc.comp (continuous_inverseTranspose n₁ ℝ)) (matrixTransform b Φ).continuous hh
    obtain ⟨hB, hEq⟩ := hcF (Q ∘ e) (hm.comp e.measurable) (he.integrable_comp_of_integrable hQ)
    let q := MeasurableEquiv.prodCongr (MeasurableEquiv.refl (unitaryCompact ℝ n₁))
      (MeasurableEquiv.inv (Fin n₁ → ℝˣ))
    have hq : MeasurePreserving q η η :=
      (MeasurePreserving.id κ).prod (realDiagonalHaar_measurePreserving_inv n₁)
    let B₀ (p : unitaryCompact ℝ n₁ × (Fin n₁ → ℝˣ)) :=
      ∫ X, Q (e (triangularPoint p.2 X p.1)) ∂upperEntryProductMeasure ν n₁
    have hcomp : Integrable (B₀ ∘ q) η := hq.integrable_comp_of_integrable hB
    have hexpand : (B₀ ∘ q) = _ := funext fun p => integral_realMatrixWeighted_dual b hf Φ h p.2 p.1
    rw [hexpand] at hcomp
    refine ⟨hcomp, ?_⟩
    rw [← he.integral_comp' Q]
    change (∫ g, (Q ∘ e) g ∂μ) = _
    rw [hEq]
    change (c : ℂ) * ∫ p, B₀ p ∂η = _
    rw [← hq.integral_comp' B₀]
    change (c : ℂ) * (∫ p, (B₀ ∘ q) p ∂η) = _
    rw [hexpand]

end Langlands.GodementJacquet
