import Langlands.Representation.GodementJacquet.ComplexMatrixCompactAverage
import Langlands.Representation.GodementJacquet.ComplexTriangularMatchedZeta
import Langlands.Representation.GodementJacquet.ComplexDiagonalHaar

/-! # The matrix integrals as a pair of fixed diagonal tests -/

noncomputable section

open MeasureTheory Topology
open scoped NNReal ENNReal Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "J" => UpperEntryPair n
local notation "M" => Matrix I I ℂ
local notation "G" => GeneralLinear n ℂ
local notation "D" => I → ℂˣ
local notation "Z" => I → ℂ
local notation "U" => upperUnipotent n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "ι" => inverseTranspose n ℂ

local instance averagedZetaGLMeasurable (m : ℕ) : MeasurableSpace (GeneralLinear m ℂ) := borel _
local instance averagedZetaGLBorel (m : ℕ) : BorelSpace (GeneralLinear m ℂ) := ⟨rfl⟩
local instance averagedZetaGLSecondCountable (m : ℕ) : SecondCountableTopology (GeneralLinear m ℂ) :=
  (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m).isInducing.secondCountableTopology
local instance averagedZetaUnitsMeasurable : MeasurableSpace ℂˣ := borel _
local instance averagedZetaUnitsBorel : BorelSpace ℂˣ := ⟨rfl⟩
local instance averagedZetaUnitsSecondCountable : SecondCountableTopology ℂˣ :=
  (Units.isOpenEmbedding_val (R := ℂ)).isInducing.secondCountableTopology
local instance averagedZetaScalarHaar (a : ℂˣ) : (complexSelfDualMeasure a).measure.IsAddHaarMeasure :=
  (complexSelfDualMeasure a).isAddHaar

private theorem continuous_restrict_unitary {f : G → ℂ} (hf : Continuous f) :
    Continuous (fun k : Kc => f k.val) := hf.comp continuous_subtype_val

private theorem integrable_restrict_unitary (μK : Measure Kc) [μK.IsHaarMeasure]
    {f : G → ℂ} (hf : Continuous f) : Integrable (fun k : Kc => f k.val) μK := by
  let : CompactSpace Kc := ComplexDuality.compactSpace_unitaryCompact n
  exact (continuous_restrict_unitary hf).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem integral_compact_matrixZetaPrimal (μK : Measure Kc)
    {χ : ℕ → ℂˣ → ℂ} {f : G → ℂ} (hf : f ∈ principalSeries ℂ n χ)
    (Φ : SchwartzMap M ℂ) (hκ : Integrable (fun k : Kc => f k.val) μK)
    (d : D) (u : U) (s : ℂ) :
    (∫ k : Kc, complexMatrixZetaIntegrand f Φ s
      (diagonalMatrixUnits ℂ d * u.val * k.val) ∂μK) =
      complexMatrixCompactAverage μK (fun k => f k.val) hκ Φ
        (diagonalMatrixUnits ℂ d * u.val : G).val *
      principalSeriesCharacter ℂ n χ d *
      detPower complexNormalizedAbs (diagonalMatrixUnits ℂ d * u.val) (s + (r : ℂ) / 2) := by
  let w := s + (r : ℂ) / 2
  let g := diagonalMatrixUnits ℂ d * u.val
  have hdet (k : Kc) : detPower complexNormalizedAbs (g * k.val) w =
      detPower complexNormalizedAbs g w := by
    rw [detPower_diagonal_unipotent_unitary d u k]
    simpa only [Subgroup.coe_one, mul_one, g] using
      (detPower_diagonal_unipotent_unitary d u (1 : Kc) w).symm
  have he (k : Kc) : complexMatrixZetaIntegrand f Φ s (g * k.val) =
      (f k.val * Φ (g.val * k.val.val)) *
        (principalSeriesCharacter ℂ n χ d * detPower complexNormalizedAbs g w) := by
    rw [complexMatrixZetaIntegrand, hdet k, Units.val_mul,
      show f (g * k.val) = principalSeriesCharacter ℂ n χ d * f k.val from hf.2 d u k.val]
    ring
  change (∫ k : Kc, complexMatrixZetaIntegrand f Φ s (g * k.val) ∂μK) = _
  simp_rw [he, integral_mul_const, ← complexMatrixCompactAverage_apply μK _ hκ Φ g.val]
  ring

private theorem integral_compact_matrixZetaDual (a : ℂˣ) (μK : Measure Kc) [SFinite μK]
    {χ : ℕ → ℂˣ → ℂ} {f : G → ℂ} (hf : f ∈ principalSeries ℂ n χ)
    (Φ : SchwartzMap M ℂ) (hκ : Integrable (fun k : Kc => f k.val) μK)
    (d : D) (u : U) (s : ℂ) :
    (∫ k : Kc, complexMatrixZetaIntegrand (f ∘ ι) (complexMatrixFourier a Φ) s
      (ι (diagonalMatrixUnits ℂ d⁻¹ * u.val * k.val)) ∂μK) =
      complexMatrixFourier a (complexMatrixCompactAverage μK (fun k => f k.val) hκ Φ)
        (ι (diagonalMatrixUnits ℂ d⁻¹ * u.val)).val *
      principalSeriesCharacter ℂ n χ d⁻¹ *
      detPower complexNormalizedAbs (ι (diagonalMatrixUnits ℂ d⁻¹ * u.val)) (s + (r : ℂ) / 2) := by
  let w := s + (r : ℂ) / 2
  let g := diagonalMatrixUnits ℂ d⁻¹ * u.val
  have hdet (k : Kc) : detPower complexNormalizedAbs (ι (g * k.val)) w =
      detPower complexNormalizedAbs (ι g) w := by
    simp only [detPower_complex_inverseTranspose]
    rw [detPower_diagonal_unipotent_unitary d⁻¹ u k]
    simpa only [Subgroup.coe_one, mul_one, g] using
      (detPower_diagonal_unipotent_unitary d⁻¹ u (1 : Kc) (-w)).symm
  have he (k : Kc) : complexMatrixZetaIntegrand (f ∘ ι) (complexMatrixFourier a Φ) s (ι (g * k.val)) =
      (f k.val * complexMatrixFourier a Φ ((ι g).val * (ι k.val).val)) *
        (principalSeriesCharacter ℂ n χ d⁻¹ * detPower complexNormalizedAbs (ι g) w) := by
    rw [complexMatrixZetaIntegrand, Function.comp_apply, inverseTranspose_involutive,
      show f (g * k.val) = principalSeriesCharacter ℂ n χ d⁻¹ * f k.val from hf.2 d⁻¹ u k.val,
      hdet k, map_mul, Units.val_mul]
    ring
  change (∫ k : Kc, complexMatrixZetaIntegrand (f ∘ ι) (complexMatrixFourier a Φ) s
    (ι (g * k.val)) ∂μK) = _
  simp_rw [he, integral_mul_const, ← complexMatrixFourier_compactAverage a μK _ hκ
    (continuous_restrict_unitary (continuous_complexPrincipalSeries hf)) Φ (ι g).val]
  ring

/-- A single pair of Fourier-related diagonal Schwartz tests computes both
matrix zeta integrals, with one common positive Haar constant. -/
theorem exists_complexMatrixZeta_diagonalTests (a : ℂˣ)
    (μK : Measure Kc) [μK.IsHaarMeasure] [SFinite μK] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (χ : ℕ → ℂˣ → ℂ) (f : G → ℂ),
      f ∈ principalSeries ℂ n χ → ∀ (Φ : SchwartzMap M ℂ),
      ∃ (A Af : SchwartzMap Z ℂ), (Af : Z → ℂ) = complexCoordinateFourier a A ∧
        let μ := complexMatrixHaar n (complexMatrixAddMeasure n a)
        (∀ s, Integrable (complexMatrixZetaIntegrand f Φ s) μ →
          (∫ g, complexMatrixZetaIntegrand f Φ s g ∂μ) =
            ((c : ℝ) : ℂ) * ∫ d : D, complexDiagonalZetaWeight χ d s *
              A (complexDiagonalVal d) ∂complexDiagonalHaar a) ∧
        (∀ s, Integrable (complexMatrixZetaIntegrand (f ∘ ι) (complexMatrixFourier a Φ) s) μ →
          (∫ g, complexMatrixZetaIntegrand (f ∘ ι) (complexMatrixFourier a Φ) s g ∂μ) =
            ((c : ℝ) : ℂ) * ∫ d : D, complexDiagonalZetaWeight (fun i z => χ i z⁻¹) d s *
              Af (complexDiagonalVal d) ∂complexDiagonalHaar a) := by
  let ν := complexSelfDualMeasure a
  let μ := complexMatrixHaar n (complexMatrixAddMeasure n a)
  let μD : Measure D := complexDiagonalHaar a
  let μU := (upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℂ)).symm
  obtain ⟨c, hc, htri⟩ := exists_complexMatrixHaar_integral_triangular_compactFirst
    (complexMatrixAddMeasure n a) μD ν μK
  refine ⟨c, hc, fun χ f hf Φ => ?_⟩
  have hfc := continuous_complexPrincipalSeries hf
  have hκ := integrable_restrict_unitary μK hfc
  let P := complexMatrixCompactAverage μK (fun k : Kc => f k.val) hκ Φ
  let A := complexUpperMarginal a P (1 : Kc)
  obtain ⟨Af, hAf⟩ := exists_schwartz_complexCoordinateFourier a A
  refine ⟨A, Af, hAf, ?_, ?_⟩
  · intro s hs
    rw [htri _ (measurable_complexMatrixZetaIntegrand hfc Φ.continuous s) hs]
    congr 1
    apply integral_congr_ae
    exact ae_of_all μD fun d => by
      simp_rw [integral_compact_matrixZetaPrimal μK hf Φ hκ d]
      have h := integral_complexZeta_character_unipotent ν χ P.continuous d (1 : Kc) 1 s
      simp only [Subgroup.coe_one, mul_one, Units.val_one] at h
      have hd : complexDiagonalVal d = (fun i : I => (d i : ℂ)) := rfl
      simpa only [A, complexUpperMarginal_apply, P, hd, Subgroup.coe_one,
        Units.val_one, Matrix.mul_one, upperEntryProductMeasure, complexCoordinateMeasure, ν] using h
  · intro s hs
    let e := (inverseTransposeContinuous n ℂ).toHomeomorph.toMeasurableEquiv
    have he : MeasurePreserving e μ μ :=
      complexMatrixHaar_measurePreserving_inverseTranspose n (complexMatrixAddMeasure n a)
    obtain ⟨Φf, hΦf⟩ := exists_schwartz_complexMatrixFourier a Φ
    obtain ⟨Pf, hPf⟩ := exists_schwartz_complexMatrixFourier a P
    have hΦfc : Continuous (complexMatrixFourier a Φ) := by
      rw [← show (Φf : M → ℂ) = complexMatrixFourier a Φ from hΦf]
      exact Φf.continuous
    have hPfc : Continuous (complexMatrixFourier a P) := by
      rw [← show (Pf : M → ℂ) = complexMatrixFourier a P from hPf]
      exact Pf.continuous
    let H := complexMatrixZetaIntegrand (f ∘ ι) (complexMatrixFourier a Φ) s
    have hH : Measurable H := measurable_complexMatrixZetaIntegrand
      (hfc.comp (continuous_inverseTranspose n ℂ)) hΦfc s
    have hI : Integrable (H ∘ e) μ := he.integrable_comp_of_integrable hs
    change (∫ g, H g ∂μ) = _
    rw [← he.integral_comp' H]
    change (∫ g, (H ∘ e) g ∂complexMatrixHaar n (complexMatrixAddMeasure n a)) = _
    rw [htri (H ∘ e) (hH.comp e.measurable) hI]
    congr 1
    let B (d : D) := ∫ u : U, ∫ k : Kc,
      H (ι (diagonalMatrixUnits ℂ d * u.val * k.val)) ∂μK ∂μU
    change (∫ d, B d ∂μD) = _
    rw [← (complexDiagonal_measurePreserving_inv n μD).integral_comp
      (MeasurableEquiv.inv D).measurableEmbedding B]
    apply integral_congr_ae
    exact ae_of_all μD fun d => by
      change B d⁻¹ = _
      simp_rw [B, H, integral_compact_matrixZetaDual a μK hf Φ hκ d]
      have ht := integral_complexDualZeta_character_unipotent a χ hPfc d (1 : Kc) 1 s
      simp only [Subgroup.coe_one, mul_one, map_one, Units.val_one] at ht
      have hM := integral_complexMatrixFourier_lower_unitary a P (1 : Kc) (complexDiagonalVal d)
      simp only [Subgroup.coe_one, map_one, Units.val_one, Matrix.mul_one] at hM
      change _ = complexCoordinateFourier a A (complexDiagonalVal d) at hM
      rw [← hAf] at hM
      rw [← hM]
      exact ht

end Langlands.GodementJacquet
