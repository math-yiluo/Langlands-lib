import Langlands.Group.GL.UpperBruhatCells
import Langlands.Representation.GodementJacquet.ComplexTriangularZetaWeight

/-! # The triangular integral for a complex principal series coefficient -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped NNReal ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.HarmonicAnalysis

local instance triangularIntegralGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n ℂ) := borel _
local instance triangularIntegralGLBorel (n : ℕ) : BorelSpace (GeneralLinear n ℂ) := ⟨rfl⟩
local instance triangularIntegralMatrixSecondCountable (n : ℕ) : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
local instance triangularIntegralMatrixBorel (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
local instance triangularIntegralGLSecondCountable (n : ℕ) : SecondCountableTopology (GeneralLinear n ℂ) :=
  (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).isInducing.secondCountableTopology
local instance triangularIntegralUnitsMeasurable : MeasurableSpace (ℂˣ) := borel _
local instance triangularIntegralUnitsBorel : BorelSpace (ℂˣ) := ⟨rfl⟩
local instance triangularIntegralUnitsSecondCountable : SecondCountableTopology ℂˣ :=
  (show IsEmbedding (Units.val : ℂˣ → ℂ) from Units.isEmbedding_val₀).isInducing.secondCountableTopology

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "J" => UpperEntryPair n
local notation "M" => Matrix I I ℂ
local notation "G" => GeneralLinear n ℂ
local notation "D" => I → ℂˣ
local notation "U" => upperUnipotent n ℂ
local notation "Kc" => unitaryCompact ℂ n

/-- A single comparison of the Haar measures works for every integrable
kernel in diagonal, unipotent and unitary coordinates. -/
theorem exists_complexMatrixHaar_integral_triangular
    (μ : Measure M) [μ.IsAddHaarMeasure] (μD : Measure D) [μD.IsHaarMeasure] [SFinite μD]
    (ν : AdditiveHaarMeasure ℂ) [SigmaFinite ν.measure]
    (μK : Measure Kc) [μK.IsHaarMeasure] [SFinite μK] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ H : G → ℂ, Measurable H → Integrable H (complexMatrixHaar n μ) →
      (∫ g, H g ∂complexMatrixHaar n μ) =
        ((c : ℝ) : ℂ) * ∫ k : Kc, ∫ d : D, ∫ u : U,
          H (diagonalMatrixUnits ℂ d * u.val * k.val)
          ∂(upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℂ)).symm ∂μD ∂μK := by
  let μU := (upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℂ)).symm
  let : μU.IsHaarMeasure := upperEntryProductMeasure_isHaar ν
  let : SFinite μU := inferInstanceAs
    (SFinite ((upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℂ)).symm))
  obtain ⟨c, hc, hμ⟩ := exists_complexMatrixHaar_eq_triangular n μ μD μU μK
  refine ⟨c, hc, fun H hH hInt => ?_⟩
  let p : (D × U) × Kc → G :=
    fun x => diagonalMatrixUnits ℂ x.1.1 * x.1.2.val * x.2.val
  let η := (μD.prod μU).prod μK
  have hd : Measurable (diagonalMatrixUnits ℂ : D → G) :=
    (continuous_diagonalUnits n (K := ℂ)).measurable
  have hp : Measurable p := ((hd.comp measurable_fst.fst).mul
    (measurable_subtype_coe.comp measurable_fst.snd)).mul
      (measurable_subtype_coe.comp measurable_snd)
  have hInt' : Integrable H (η.map p) := by
    rw [hμ] at hInt
    exact (integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).1 hInt
  have hHp : Integrable (fun x => H (p x)) η :=
    (integrable_map_measure hH.aestronglyMeasurable hp.aemeasurable).1 hInt'
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul,
    integral_map hp.aemeasurable hH.aestronglyMeasurable]
  congr 1
  rw [integral_prod_symm _ hHp]
  apply integral_congr_ae
  filter_upwards [hHp.prod_left_ae] with k hk
  exact integral_prod _ hk

/-- The same triangular integral with the compact variable integrated first. -/
theorem exists_complexMatrixHaar_integral_triangular_compactFirst
    (μ : Measure M) [μ.IsAddHaarMeasure] (μD : Measure D) [μD.IsHaarMeasure] [SFinite μD]
    (ν : AdditiveHaarMeasure ℂ) [SigmaFinite ν.measure]
    (μK : Measure Kc) [μK.IsHaarMeasure] [SFinite μK] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ H : G → ℂ, Measurable H → Integrable H (complexMatrixHaar n μ) →
      (∫ g, H g ∂complexMatrixHaar n μ) =
        ((c : ℝ) : ℂ) * ∫ d : D, ∫ u : U, ∫ k : Kc,
          H (diagonalMatrixUnits ℂ d * u.val * k.val) ∂μK
          ∂(upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℂ)).symm ∂μD := by
  let μU := (upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℂ)).symm
  let : μU.IsHaarMeasure := upperEntryProductMeasure_isHaar ν
  let : SFinite μU := inferInstanceAs
    (SFinite ((upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℂ)).symm))
  obtain ⟨c, hc, hμ⟩ := exists_complexMatrixHaar_eq_triangular n μ μD μU μK
  refine ⟨c, hc, fun H hH hInt => ?_⟩
  let p : (D × U) × Kc → G :=
    fun x => diagonalMatrixUnits ℂ x.1.1 * x.1.2.val * x.2.val
  let η := (μD.prod μU).prod μK
  have hd : Measurable (diagonalMatrixUnits ℂ : D → G) :=
    (continuous_diagonalUnits n (K := ℂ)).measurable
  have hp : Measurable p := ((hd.comp measurable_fst.fst).mul
    (measurable_subtype_coe.comp measurable_fst.snd)).mul
      (measurable_subtype_coe.comp measurable_snd)
  have hInt' : Integrable H (η.map p) := by
    rw [hμ] at hInt
    exact (integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).1 hInt
  have hHp : Integrable (fun x => H (p x)) η :=
    (integrable_map_measure hH.aestronglyMeasurable hp.aemeasurable).1 hInt'
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul,
    integral_map hp.aemeasurable hH.aestronglyMeasurable]
  rw [integral_prod _ hHp, integral_prod _ hHp.integral_prod_left]

theorem measurable_complexDetPower (s : ℂ) :
    Measurable (fun g : G => detPower complexNormalizedAbs g s) := by
  have hdet : Continuous (fun g : G => g.val.det) :=
    Units.continuous_val.comp Matrix.GeneralLinearGroup.continuous_det
  have hB : Measurable (fun g : G => Real.log (complexNormalizedAbs g.val.det)) :=
    Real.measurable_log.comp (hdet.norm.pow 2).measurable
  exact Complex.continuous_exp.measurable.comp
    (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hB))

theorem continuous_complexPrincipalSeries {χ : ℕ → ℂˣ → ℂ} {f : G → ℂ}
    (hf : f ∈ principalSeries ℂ n χ) : Continuous f :=
  hf.1.continuous

/-- Change from the upper-unipotent factor to actual matrix entries after
factoring out the principal series character. -/
theorem integral_complexZeta_character_unipotent (ν : AdditiveHaarMeasure ℂ) [SigmaFinite ν.measure]
    (χ : ℕ → ℂˣ → ℂ) {Φ : M → ℂ} (hΦ : Continuous Φ) (d : D) (k : Kc) (v s : ℂ) :
    (∫ u : U,
      Φ (diagonalMatrixUnits ℂ d * u.val * k.val : G).val * (principalSeriesCharacter ℂ n χ d * v) *
          detPower complexNormalizedAbs (diagonalMatrixUnits ℂ d * u.val * k.val)
            (s + (r : ℂ) / 2)
      ∂(upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℂ)).symm) =
      (complexDiagonalZetaWeight χ d s * v) *
        ∫ X : J → ℂ, Φ (complexTriangularMatrix (fun i => (d i : ℂ)) X * k.val.val)
          ∂upperEntryProductMeasure ν n := by
  let E := (upperEntryCoordinates n (K := ℂ)).symm.toMeasurableEquiv
  change (∫ u : U, _ ∂(upperEntryProductMeasure ν n).map E) = _
  rw [E.measurableEmbedding.integral_map]
  let δ := diagonalMatrixUnits ℂ d
  let t := detPower complexNormalizedAbs (δ * (1 : U).val * k.val) (s + (r : ℂ) / 2)
  have hdet (u : U) : detPower complexNormalizedAbs (δ * u.val * k.val) (s + (r : ℂ) / 2) = t :=
    (detPower_diagonal_unipotent_unitary d u k _).trans
      (detPower_diagonal_unipotent_unitary d 1 k _).symm
  let F (X : M) := Φ (X * k.val.val)
  have hF : Continuous F := hΦ.comp (continuous_id.mul continuous_const)
  change (∫ X : J → ℂ, F (δ.val * (E X).val.val) *
    (principalSeriesCharacter ℂ n χ d * v) *
      detPower complexNormalizedAbs (δ * (E X).val * k.val) (s + (r : ℂ) / 2)
    ∂upperEntryProductMeasure ν n) = _
  simp_rw [hdet, integral_mul_const]
  change (∫ X : J → ℂ, F ((diagonalMatrixUnits ℂ d).val *
      ((upperEntryCoordinates n (K := ℂ)).symm X).val.val) ∂upperEntryProductMeasure ν n) *
    (principalSeriesCharacter ℂ n χ d * v) * t = _
  rw [integral_diagonal_mul_upperEntries ν d F hF]
  have hw := complexTriangular_zetaWeight χ d 1 k s
  let c : ℂ := ((↑((∏ ij : J, complexAbsHom (d ij.1.1 : ℂ))⁻¹) : ℝ) : ℂ)
  let A := ∫ X : J → ℂ, F (complexTriangularMatrix (fun i => (d i : ℂ)) X)
    ∂upperEntryProductMeasure ν n
  change (c * A) * (principalSeriesCharacter ℂ n χ d * v) * t =
    (complexDiagonalZetaWeight χ d s * v) * A
  calc
    _ = (c * principalSeriesCharacter ℂ n χ d * t * v) * A := by ring
    _ = _ := by rw [show c * principalSeriesCharacter ℂ n χ d * t =
      complexDiagonalZetaWeight χ d s from hw]

theorem integral_complexZeta_unipotent (ν : AdditiveHaarMeasure ℂ) [SigmaFinite ν.measure]
    {χ : ℕ → ℂˣ → ℂ} {f : G → ℂ} (hf : f ∈ principalSeries ℂ n χ)
    {Φ : M → ℂ} (hΦ : Continuous Φ) (d : D) (k : Kc) (s : ℂ) :
    (∫ u : U,
      Φ (diagonalMatrixUnits ℂ d * u.val * k.val : G).val *
        f (diagonalMatrixUnits ℂ d * u.val * k.val) *
          detPower complexNormalizedAbs (diagonalMatrixUnits ℂ d * u.val * k.val)
            (s + (r : ℂ) / 2)
      ∂(upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℂ)).symm) =
      (complexDiagonalZetaWeight χ d s * f k.val) *
        ∫ X : J → ℂ, Φ (complexTriangularMatrix (fun i => (d i : ℂ)) X * k.val.val)
          ∂upperEntryProductMeasure ν n := by
  have he (u : U) : f (diagonalMatrixUnits ℂ d * u.val * k.val) =
      principalSeriesCharacter ℂ n χ d * f k.val := hf.2 d u k.val
  simp_rw [he]
  exact integral_complexZeta_character_unipotent ν χ hΦ d k (f k.val) s

/-- On a domain of absolute convergence, the matrix integral of a principal
series vector is a unitary average of diagonal integrals of matrix marginals. -/
theorem exists_complexPrincipalSeries_matrixIntegral_triangular
    (μ : Measure M) [μ.IsAddHaarMeasure] (μD : Measure D) [μD.IsHaarMeasure] [SFinite μD]
    (ν : AdditiveHaarMeasure ℂ) [SigmaFinite ν.measure]
    (μK : Measure Kc) [μK.IsHaarMeasure] [SFinite μK] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (χ : ℕ → ℂˣ → ℂ) (f : G → ℂ),
      f ∈ principalSeries ℂ n χ → ∀ (Φ : M → ℂ), Continuous Φ →
      ∀ s : ℂ, Integrable (fun g : G => Φ g.val * f g *
        detPower complexNormalizedAbs g (s + (r : ℂ) / 2)) (complexMatrixHaar n μ) →
        (∫ g : G, Φ g.val * f g * detPower complexNormalizedAbs g (s + (r : ℂ) / 2)
          ∂complexMatrixHaar n μ) =
          ((c : ℝ) : ℂ) * ∫ k : Kc, ∫ d : D, (complexDiagonalZetaWeight χ d s * f k.val) *
            (∫ X : J → ℂ, Φ (complexTriangularMatrix (fun i => (d i : ℂ)) X * k.val.val)
              ∂upperEntryProductMeasure ν n) ∂μD ∂μK := by
  obtain ⟨c, hc, hμ⟩ := exists_complexMatrixHaar_integral_triangular μ μD ν μK
  refine ⟨c, hc, fun χ f hf Φ hΦ s hInt => ?_⟩
  let H (g : G) := Φ g.val * f g * detPower complexNormalizedAbs g (s + (r : ℂ) / 2)
  have hH : Measurable H :=
    ((hΦ.measurable.comp Units.continuous_val.measurable).mul hf.1.continuous.measurable).mul
      (measurable_complexDetPower _)
  change (∫ g, H g ∂complexMatrixHaar n μ) = _
  rw [hμ H hH hInt]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun k => integral_congr_ae
    (ae_of_all _ fun d => integral_complexZeta_unipotent ν hf hΦ d k s)

end Langlands.GodementJacquet
