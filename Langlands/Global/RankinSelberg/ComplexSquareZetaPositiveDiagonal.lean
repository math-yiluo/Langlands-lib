import Langlands.Global.RankinSelberg.ComplexSquareIwasawaEntries
import Langlands.Global.RankinSelberg.ComplexGodementSection
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-! # Positive logarithmic diagonal integration for complex square zeta integrals -/

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal Matrix.Norms.Operator NNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexMaximalParabolicIntegration
  (det_upperUnipotent normSqC normSqC_det_unitary)
open ComplexGodement (normPower upperTriangularEntries)
open ComplexLocalWhittakerGauge (logTorus)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance squarePositiveGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance squarePositiveGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance squarePositiveGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Y" => Fin n → ℝ
local notation "X" => UpperEntryPair n → ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- The square matrix zeta kernel with the half-modulus shift of Jacquet's equation (4.3). -/
def zetaKernel (Φ : Mat → ℂ) (f : G → ℂ) (s : ℂ) (g : G) : ℂ :=
  Φ g.val * f g * normPower (s + ((n : ℂ) - 1) / 2) (determinant g)

private def positiveUnit (y : ℝ) : ℂˣ :=
  Units.mk0 (Real.exp y : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero y))

private theorem normPower_positiveUnit (p : ℂ) (y : ℝ) :
    normPower p (positiveUnit y) = Complex.exp (2 * p * y) := by
  change normSqC (Real.exp y : ℂ) ^ p = _
  simp only [normSqC, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]
  have hne : ((Real.exp y ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (Real.exp_ne_zero _))
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (by positivity), Real.log_pow,
    Real.log_exp]
  congr 1
  push_cast
  ring

private theorem det_logTorus (y : Y) :
    determinant (logTorus y) = ∏ i, positiveUnit (y i) := by
  apply Units.ext
  change (logTorus y).val.det = Units.coeHom ℂ (∏ i, positiveUnit (y i))
  rw [ComplexLocalWhittakerGauge.logTorus_val, Matrix.det_diagonal, map_prod]
  rfl

private theorem det_unipotent (u : N) : determinant u.val = 1 :=
  Units.ext (det_upperUnipotent u)

private theorem normPower_det_unitary (p : ℂ) (k : K) :
    normPower p (determinant k.val) = 1 := by
  change normSqC (k.val.val.det) ^ p = 1
  rw [normSqC_det_unitary k, Complex.one_cpow]

private theorem upperRowJacobian_exp (y : Y) :
    ((upperRowJacobian y : ℝ) : ℂ) =
      ∏ i : Fin n, Complex.exp (-2 * ((n - 1 - i.val : ℕ) : ℂ) * y i) := by
  rw [upperRowJacobian_coe, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_nat_mul, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The zeta kernel in additive upper-triangular entries and logarithmic positive diagonal.
The Borel half-modulus and the row Jacobian leave the ordinary Tate exponents. -/
def logarithmicKernel (ds : Fin n → ComplexCharacterData) (Φ : Mat → ℂ) (f : G → ℂ)
    (s : ℂ) (y : Y) (z : X) (k : K) : ℂ :=
  Φ (upperTriangularEntries (fun i => (Real.exp (y i) : ℂ)) z * k.val.val) * f k.val *
    ∏ i, Complex.exp (2 * (s + (ds i).exponent) * y i)

private theorem chart_weight (ds : Fin n → ComplexCharacterData) (s : ℂ) (y : Y)
    (u : N) (k : K) :
    ((upperRowJacobian y : ℝ) : ℂ) *
      principalSeriesCharacter ℂ n (complexPositionCharacter (List.ofFn ds))
        (fun i => positiveUnit (y i)) *
      normPower (s + ((n : ℂ) - 1) / 2) (determinant (logTorus y * u.val * k.val)) =
    ∏ i, Complex.exp (2 * (s + (ds i).exponent) * y i) := by
  simp only [map_mul, det_unipotent, mul_one, normPower_det_unitary, det_logTorus,
    map_prod, normPower_positiveUnit, principalSeriesCharacter_ofFn]
  change _ * (∏ i, borelFactor (ds i).weight
    (2 * (ds i).exponent + ((n : ℂ) - 1) - 2 * ((i : ℕ) : ℂ)) (Real.exp (y i) : ℂ)) * _ = _
  simp only [borelFactor_exp, upperRowJacobian_exp, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne'
  have hi : i.val ≤ n - 1 := by have := i.isLt; omega
  rw [Nat.cast_sub hi, Nat.cast_sub hn, Nat.cast_one, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

private theorem chart_kernel (ds : Fin n → ComplexCharacterData) (Φ : Mat → ℂ)
    {f : G → ℂ} (hf : f ∈ complexStandardModule n (List.ofFn ds))
    (s : ℂ) (y : Y) (u : N) (k : K) :
    ((upperRowJacobian y : ℝ) : ℂ) * zetaKernel Φ f s (logTorus y * u.val * k.val) =
      logarithmicKernel ds Φ f s y (scaleUpperRows y (upperEntryCoordinates n u)) k := by
  have h := hf.2 (fun i => positiveUnit (y i)) u k.val
  change f (logTorus y * u.val * k.val) = _ at h
  rw [zetaKernel, logarithmicKernel, Units.val_mul, logTorus_mul_unipotent_val, h]
  have hw := chart_weight ds s y u k
  rw [← hw]
  ring

private theorem integral_chart_slice
    (ds : Fin n → ComplexCharacterData) (Φ : Mat → ℂ) (hΦ : Continuous Φ)
    {f : G → ℂ} (hf : f ∈ complexStandardModule n (List.ofFn ds))
    (s : ℂ) (y : Y) (k : K) :
    (∫ z : X, zetaKernel Φ f s (logTorus y * ((upperEntryCoordinates n).symm z).val * k.val)) =
      ∫ z : X, logarithmicKernel ds Φ f s y z k := by
  let F : X → ℂ := fun z => logarithmicKernel ds Φ f s y z k
  let J : ℂ := ((upperRowJacobian y : ℝ) : ℂ)
  have hJ : J ≠ 0 := Complex.ofReal_ne_zero.mpr
    (show 0 < (upperRowJacobian y : ℝ) from upperRowJacobian_pos y).ne'
  have hscale : Continuous (scaleUpperRows y) := by
    refine continuous_pi fun i => ?_
    change Continuous (fun z : X => Real.exp (y i.1.1) • z i)
    exact (continuous_apply i : Continuous (fun z : X => z i)).const_smul (Real.exp (y i.1.1))
  have htri : Continuous (upperTriangularEntries (fun i => (Real.exp (y i) : ℂ))) := by
    apply continuous_matrix
    intro i j
    by_cases h : i < j
    · simp only [upperTriangularEntries, dite_eq_left h]
      exact continuous_apply (⟨(i, j), h⟩ : UpperEntryPair n)
    · simp only [upperTriangularEntries, dite_eq_right h]
      exact continuous_const
  have hF : Continuous F :=
    ((hΦ.comp (htri.matrix_mul continuous_const)).mul continuous_const).mul continuous_const
  apply mul_left_cancel₀ hJ
  calc
    _ = ∫ z : X, J * zetaKernel Φ f s (logTorus y * ((upperEntryCoordinates n).symm z).val * k.val) :=
      (integral_const_mul _ _).symm
    _ = ∫ z : X, F (scaleUpperRows y z) := by
      apply integral_congr_ae
      filter_upwards with z
      simpa only [J, F, Homeomorph.apply_symm_apply] using
        chart_kernel ds Φ hf s y ((upperEntryCoordinates n).symm z) k
    _ = ∫ z, F z ∂(volume : Measure X).map (scaleUpperRows y) :=
      (integral_map hscale.measurable.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by
      rw [map_scaleUpperRows, integral_smul_nnreal_measure]
      simp only [NNReal.smul_def, Complex.real_smul, J]
      rfl

/-- On the domain of absolute convergence, the square zeta integral is a fixed positive
multiple of its upper triangular expression, with the Tate weights in the diagonal entries. -/
def ComplexSquareZetaPositiveDiagonalStatement : Prop :=
  ∀ (μ : Measure G) (κ : Measure K), μ.IsHaarMeasure → κ.IsHaarMeasure →
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (ds : Fin n → ComplexCharacterData) (Φ : Mat → ℂ) (f : G → ℂ),
      Continuous Φ → f ∈ complexStandardModule n (List.ofFn ds) → ∀ s : ℂ,
        Integrable (zetaKernel Φ f s) μ →
        (∫ g, zetaKernel Φ f s g ∂μ) =
          (c : ℂ) * ∫ y : Y, ∫ k, (∫ z : X, logarithmicKernel ds Φ f s y z k) ∂κ

theorem complexSquareZetaPositiveDiagonal : ComplexSquareZetaPositiveDiagonalStatement (n := n) := by
  intro μ κ hμ hκ
  let : κ.IsHaarMeasure := hκ
  obtain ⟨c, hc, hchart⟩ := complexSquareIwasawaEntries μ κ hμ hκ
  refine ⟨c, hc, fun ds Φ f hΦ hf s hI => ?_⟩
  let I := zetaKernel Φ f s
  let η := (volume : Measure Y).prod (κ.prod (volume : Measure X))
  let q : Y × (K × X) → G := fun p =>
    logTorus p.1 * ((upperEntryCoordinates n).symm p.2.2).val * p.2.1.val
  have hqm : Measurable q :=
    ((ComplexLocalIwasawa.continuous_logTorus.measurable.comp measurable_fst).mul
      (measurable_subtype_coe.comp ((upperEntryCoordinates n).symm.measurable.comp
        (measurable_snd.comp measurable_snd)))).mul
      (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd))
  have hμ' : μ = c • η.map q := by
    let e : (Y × X) × K → Y × (K × X) := Prod.map id Prod.swap ∘ MeasurableEquiv.prodAssoc
    have he : MeasurePreserving e (((volume : Measure Y).prod (volume : Measure X)).prod κ) η :=
      ((MeasurePreserving.id (volume : Measure Y)).prod
        (Measure.measurePreserving_swap (μ := (volume : Measure X)) (ν := κ))).comp
        (measurePreserving_prodAssoc volume volume κ)
    rw [← he.map_eq, Measure.map_map hqm he.measurable]
    exact hchart
  change Integrable I μ at hI
  rw [hμ'] at hI
  have hI' : Integrable I (η.map q) :=
    (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hc.ne') ENNReal.coe_ne_top).mp hI
  have hcomp := (integrable_map_measure hI'.aestronglyMeasurable hqm.aemeasurable).mp hI'
  have hFubini := integral_prod (I ∘ q) hcomp
  change (∫ x, I (q x) ∂η) = _ at hFubini
  change (∫ g, I g ∂μ) = _
  rw [hμ', integral_smul_nnreal_measure, integral_map hqm.aemeasurable
    hI'.aestronglyMeasurable, hFubini]
  simp only [NNReal.smul_def, Complex.real_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [hcomp.prod_right_ae] with y hy
  rw [integral_prod _ hy]
  apply integral_congr_ae
  filter_upwards with k
  exact integral_chart_slice ds Φ hΦ hf s y k

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
