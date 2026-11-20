import Langlands.Representation.GodementJacquet.ComplexTriangularDualWeight
import Langlands.Representation.GodementJacquet.ComplexTriangularHaarInversion
import Langlands.Representation.GodementJacquet.ComplexTriangularMatchedTests
import Langlands.Representation.GodementJacquet.ComplexTriangularZetaIntegral

/-! # Matched diagonal expansions of the primal and dual complex matrix zeta integrals -/

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
local notation "U" => upperUnipotent n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "ι" => inverseTranspose n ℂ

local instance matchedZetaGLMeasurable (m : ℕ) : MeasurableSpace (GeneralLinear m ℂ) := borel _
local instance matchedZetaGLBorel (m : ℕ) : BorelSpace (GeneralLinear m ℂ) := ⟨rfl⟩
local instance matchedZetaMatrixSecondCountable (m : ℕ) : SecondCountableTopology (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℂ))
local instance matchedZetaMatrixBorel (m : ℕ) : BorelSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (BorelSpace (Fin m → Fin m → ℂ))
local instance matchedZetaGLSecondCountable (m : ℕ) : SecondCountableTopology (GeneralLinear m ℂ) :=
  (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m).isInducing.secondCountableTopology
local instance matchedZetaUnitsMeasurable : MeasurableSpace ℂˣ := borel _
local instance matchedZetaUnitsBorel : BorelSpace ℂˣ := ⟨rfl⟩
local instance matchedZetaUnitsSecondCountable : SecondCountableTopology ℂˣ :=
  (show IsEmbedding (Units.val : ℂˣ → ℂ) from Units.isEmbedding_val₀).isInducing.secondCountableTopology
local instance matchedZetaScalarHaar (a : ℂˣ) : (complexSelfDualMeasure a).measure.IsAddHaarMeasure :=
  (complexSelfDualMeasure a).isAddHaar

theorem inverseTranspose_triangularPoint (d : D) (u : U) (k : Kc) :
    (ι (diagonalMatrixUnits ℂ d⁻¹ * (u⁻¹).val * k.val)).val =
      (u.val.val * (diagonalMatrixUnits ℂ d).val).transpose * (ι k.val).val := by
  have hd : ι (diagonalMatrixUnits ℂ d⁻¹) = diagonalMatrixUnits ℂ d := by
    apply Units.ext
    rw [inverseTranspose_coe, ← map_inv, inv_inv, diagonalMatrixUnits_val, Matrix.diagonal_transpose]
  rw [map_mul, map_mul, hd, Units.val_mul, Units.val_mul, Matrix.transpose_mul,
    inverseTranspose_coe, Subgroup.coe_inv, inv_inv, diagonalMatrixUnits_val, Matrix.diagonal_transpose]

/-- The dual change to actual strict entries, after factoring out the
principal series character on the inverted diagonal. -/
theorem integral_complexDualZeta_character_unipotent (a : ℂˣ)
    (χ : ℕ → ℂˣ → ℂ) {Ψ : M → ℂ} (hΨ : Continuous Ψ) (d : D) (k : Kc) (v s : ℂ) :
    (∫ u : U,
      Ψ (ι (diagonalMatrixUnits ℂ d⁻¹ * u.val * k.val)).val *
        (principalSeriesCharacter ℂ n χ d⁻¹ * v) *
          detPower complexNormalizedAbs (ι (diagonalMatrixUnits ℂ d⁻¹ * u.val * k.val))
            (s + (r : ℂ) / 2)
      ∂(upperEntryProductMeasure (complexSelfDualMeasure a) n).map
        (upperEntryCoordinates n (K := ℂ)).symm) =
      (complexDiagonalZetaWeight (fun i z => χ i z⁻¹) d s * v) *
        ∫ X : J → ℂ, Ψ ((complexTriangularMatrix (fun i => (d i : ℂ)) X).transpose *
          (ι k.val).val) ∂complexCoordinateMeasure J a := by
  let ν := complexSelfDualMeasure a
  let E := (upperEntryCoordinates n (K := ℂ)).symm.toMeasurableEquiv
  let μU := (upperEntryProductMeasure ν n).map E
  let δ := diagonalMatrixUnits ℂ d⁻¹
  let w := s + (r : ℂ) / 2
  let H (u : U) := Ψ (ι (δ * u.val * k.val)).val *
    (principalSeriesCharacter ℂ n χ d⁻¹ * v) * detPower complexNormalizedAbs (ι (δ * u.val * k.val)) w
  have hμ : MeasurePreserving (Inv.inv : U → U) μU μU :=
    upperEntryProductMeasure_measurePreserving_inv n ν
  change (∫ u, H u ∂μU) = _
  rw [← hμ.integral_comp (MeasurableEquiv.inv U).measurableEmbedding H]
  change (∫ u, H u⁻¹ ∂(upperEntryProductMeasure ν n).map E) = _
  rw [E.measurableEmbedding.integral_map]
  let F (X : M) := Ψ (X.transpose * (ι k.val).val)
  have hF : Continuous F := hΨ.comp (continuous_id.matrix_transpose.matrix_mul continuous_const)
  let t := detPower complexNormalizedAbs (ι (δ * (1 : U).val * k.val)) w
  have hdet (u : U) : detPower complexNormalizedAbs (ι (δ * u.val * k.val)) w = t := by
    simp only [t, detPower_complex_inverseTranspose, δ, detPower_diagonal_unipotent_unitary]
  have he (u : U) :
      H u⁻¹ = F (u.val.val * (diagonalMatrixUnits ℂ d).val) *
        (principalSeriesCharacter ℂ n χ d⁻¹ * v) * t := by
    dsimp only [H]
    rw [inverseTranspose_triangularPoint, hdet]
  simp_rw [he, integral_mul_const]
  change (∫ X, F (((upperEntryCoordinates n (K := ℂ)).symm X).val.val *
    (diagonalMatrixUnits ℂ d).val) ∂upperEntryProductMeasure ν n) *
      (principalSeriesCharacter ℂ n χ d⁻¹ * v) * t = _
  rw [integral_upperEntries_mul_diagonal ν d F hF]
  have hw := complexTriangular_dualZetaWeight χ d 1 k s
  let c : ℂ := ((↑((∏ ij : J, complexAbsHom (d ij.1.2 : ℂ))⁻¹) : ℝ) : ℂ)
  let B := ∫ X : J → ℂ, F (complexTriangularMatrix (fun i => (d i : ℂ)) X)
    ∂upperEntryProductMeasure ν n
  change (c * B) * (principalSeriesCharacter ℂ n χ d⁻¹ * v) * t =
    (complexDiagonalZetaWeight (fun i z => χ i z⁻¹) d s * v) * B
  calc
    _ = (c * principalSeriesCharacter ℂ n χ d⁻¹ * t * v) * B := by ring
    _ = _ := by rw [show c * principalSeriesCharacter ℂ n χ d⁻¹ * t =
      complexDiagonalZetaWeight (fun i z => χ i z⁻¹) d s from hw]

private theorem integral_complexDualZeta_unipotent (a : ℂˣ)
    {χ : ℕ → ℂˣ → ℂ} {f : G → ℂ} (hf : f ∈ principalSeries ℂ n χ)
    {Ψ : M → ℂ} (hΨ : Continuous Ψ) (d : D) (k : Kc) (s : ℂ) :
    (∫ u : U,
      Ψ (ι (diagonalMatrixUnits ℂ d⁻¹ * u.val * k.val)).val *
        f (diagonalMatrixUnits ℂ d⁻¹ * u.val * k.val) *
          detPower complexNormalizedAbs (ι (diagonalMatrixUnits ℂ d⁻¹ * u.val * k.val))
            (s + (r : ℂ) / 2)
      ∂(upperEntryProductMeasure (complexSelfDualMeasure a) n).map
        (upperEntryCoordinates n (K := ℂ)).symm) =
      (complexDiagonalZetaWeight (fun i z => χ i z⁻¹) d s * f k.val) *
        ∫ X : J → ℂ, Ψ ((complexTriangularMatrix (fun i => (d i : ℂ)) X).transpose *
          (ι k.val).val) ∂complexCoordinateMeasure J a := by
  have he (u : U) : f (diagonalMatrixUnits ℂ d⁻¹ * u.val * k.val) =
      principalSeriesCharacter ℂ n χ d⁻¹ * f k.val := hf.2 d⁻¹ u k.val
  simp_rw [he]
  exact integral_complexDualZeta_character_unipotent a χ hΨ d k (f k.val) s

/-- The shifted integrand on the matrix group in the complex matrix zeta integral. -/
def complexMatrixZetaIntegrand (f : G → ℂ) (Φ : M → ℂ) (s : ℂ) (g : G) : ℂ :=
  Φ g.val * f g * detPower complexNormalizedAbs g (s + (r : ℂ) / 2)

theorem measurable_complexMatrixZetaIntegrand {f : G → ℂ} (hf : Continuous f)
    {Φ : M → ℂ} (hΦ : Continuous Φ) (s : ℂ) :
    Measurable (complexMatrixZetaIntegrand f Φ s) :=
  ((hΦ.measurable.comp Units.continuous_val.measurable).mul hf.measurable).mul
    (measurable_complexDetPower _)

/-- A single Haar comparison constant gives the primal matrix integral and
the inverse-transpose dual integral as unitary averages of matched tests on
the diagonal, on their respective domains of absolute convergence. -/
theorem exists_complexMatrixZeta_matchedTriangular (a : ℂˣ)
    (μD : Measure D) [μD.IsHaarMeasure] [SFinite μD]
    (μK : Measure Kc) [μK.IsHaarMeasure] [SFinite μK] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (χ : ℕ → ℂˣ → ℂ) (f : G → ℂ),
      f ∈ principalSeries ℂ n χ → ∀ (Φ : SchwartzMap M ℂ),
      let μ := complexMatrixHaar n (complexMatrixAddMeasure n a)
      (∀ s, Integrable (complexMatrixZetaIntegrand f Φ s) μ →
        (∫ g, complexMatrixZetaIntegrand f Φ s g ∂μ) =
          ((c : ℝ) : ℂ) * ∫ k : Kc, ∫ d : D,
            (complexDiagonalZetaWeight χ d s * f k.val) *
              complexUpperMarginal a Φ k (fun i => (d i : ℂ)) ∂μD ∂μK) ∧
      (∀ s, Integrable (complexMatrixZetaIntegrand (f ∘ ι) (complexMatrixFourier a Φ) s) μ →
        (∫ g, complexMatrixZetaIntegrand (f ∘ ι) (complexMatrixFourier a Φ) s g ∂μ) =
          ((c : ℝ) : ℂ) * ∫ k : Kc, ∫ d : D,
            (complexDiagonalZetaWeight (fun i z => χ i z⁻¹) d s * f k.val) *
              complexCoordinateFourier a (complexUpperMarginal a Φ k)
                (fun i => (d i : ℂ)) ∂μD ∂μK) := by
  let ν := complexSelfDualMeasure a
  let μ := complexMatrixHaar n (complexMatrixAddMeasure n a)
  let μU := (upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℂ)).symm
  obtain ⟨c, hc, htri⟩ := exists_complexMatrixHaar_integral_triangular
    (complexMatrixAddMeasure n a) μD ν μK
  refine ⟨c, hc, fun χ f hf Φ => ?_⟩
  have hfc := continuous_complexPrincipalSeries hf
  constructor
  · intro s hs
    rw [htri _ (measurable_complexMatrixZetaIntegrand hfc Φ.continuous s) hs]
    congr 1
    apply integral_congr_ae
    refine ae_of_all _ fun k => integral_congr_ae (ae_of_all _ fun d => ?_)
    change (∫ u : U, complexMatrixZetaIntegrand f Φ s
      (diagonalMatrixUnits ℂ d * u.val * k.val) ∂μU) =
        (complexDiagonalZetaWeight χ d s * f k.val) *
          complexUpperMarginal a Φ k (fun i => (d i : ℂ))
    rw [complexUpperMarginal_apply]
    exact integral_complexZeta_unipotent ν hf Φ.continuous d k s
  · intro s hs
    let Ψ := complexMatrixFourier a Φ
    have hΨ : Continuous Ψ := by
      obtain ⟨Ψ', hΨ'⟩ := exists_schwartz_complexMatrixFourier a Φ
      rw [← show (Ψ' : M → ℂ) = Ψ from hΨ']
      exact Ψ'.continuous
    let e := (inverseTransposeContinuous n ℂ).toHomeomorph.toMeasurableEquiv
    have hμ : MeasurePreserving e μ μ :=
      complexMatrixHaar_measurePreserving_inverseTranspose n (complexMatrixAddMeasure n a)
    let H := complexMatrixZetaIntegrand (f ∘ ι) Ψ s
    have hH : Measurable H := measurable_complexMatrixZetaIntegrand
      (hfc.comp (continuous_inverseTranspose n ℂ)) hΨ s
    have hInt : Integrable (H ∘ e) μ := hμ.integrable_comp_of_integrable hs
    change (∫ g, H g ∂μ) = _
    rw [← hμ.integral_comp' H]
    change (∫ g, (H ∘ e) g ∂complexMatrixHaar n (complexMatrixAddMeasure n a)) = _
    rw [htri (H ∘ e) (hH.comp e.measurable) hInt]
    congr 1
    apply integral_congr_ae
    refine ae_of_all _ fun k => ?_
    let A (d : D) := ∫ u : U, H (e (diagonalMatrixUnits ℂ d * u.val * k.val)) ∂μU
    have hD := complexDiagonal_measurePreserving_inv n μD
    change (∫ d, A d ∂μD) = _
    rw [← hD.integral_comp (MeasurableEquiv.inv D).measurableEmbedding A]
    apply integral_congr_ae
    refine ae_of_all _ fun d => ?_
    have he (u : U) :
      H (e (diagonalMatrixUnits ℂ d⁻¹ * u.val * k.val)) =
        Ψ (ι (diagonalMatrixUnits ℂ d⁻¹ * u.val * k.val)).val *
          f (diagonalMatrixUnits ℂ d⁻¹ * u.val * k.val) *
            detPower complexNormalizedAbs (ι (diagonalMatrixUnits ℂ d⁻¹ * u.val * k.val))
              (s + (r : ℂ) / 2) := by
      change Ψ _ * f (ι (ι _)) * _ = _
      rw [inverseTranspose_involutive]
      rfl
    change A d⁻¹ = _
    simp only [A, he]
    rw [integral_complexDualZeta_unipotent a hf hΨ]
    congr 1
    exact integral_complexMatrixFourier_lower_unitary a Φ k (fun i => (d i : ℂ))

end Langlands.GodementJacquet
