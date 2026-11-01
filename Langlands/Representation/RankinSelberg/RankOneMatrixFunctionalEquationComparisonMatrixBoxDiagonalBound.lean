import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothDiagonalBound
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonDiagonalWeightBound
import Langlands.Representation.Hecke.TestFunction
import Langlands.Representation.Whittaker.JPSDilationAssemblyProof

/-! Weighted diagonal bounds from genuine full-matrix box integrals. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear Topology Conductor GodementJacquet HarmonicAnalysis
open scoped ENNReal NNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance boxDiagonalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance boxDiagonalValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance boxDiagonalLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance boxDiagonalT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance boxDiagonalSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance boxDiagonalMeasurable : MeasurableSpace F.Carrier := borel _
local instance boxDiagonalBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance boxDiagonalGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance boxDiagonalGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance boxDiagonalGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance boxDiagonalGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData


local instance boxDiagonalUnitsSecondCountable : SecondCountableTopology F.Carrierˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance boxDiagonalUnitsLocallyCompact : LocallyCompactSpace F.Carrierˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := F.Carrier)).locallyCompactSpace
local instance boxDiagonalUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance boxDiagonalUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩


/-- A compact open box in the full square-matrix space, including singular
matrices, defined using the canonical normalized absolute value. -/
def matrixNormBox (n : ℕ) (ρ : ℝ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
  Set.univ.pi fun _ => Set.univ.pi fun _ => {x : F.Carrier | abv x ≤ ρ}

theorem isClopen_matrixNormBox (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    IsClopen (matrixNormBox F n ρ) := by
  refine ⟨isClosed_set_pi (fun _ _ => isClosed_set_pi fun _ _ => ?_),
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => ?_)⟩
  · exact (Whittaker.JPSDilationAssembly.isClopen_le F.canonicalTopologicalData hρ).isClosed
  · exact (Whittaker.JPSDilationAssembly.isClopen_le F.canonicalTopologicalData hρ).isOpen

theorem isCompact_matrixNormBox (n : ℕ) (ρ : ℝ) : IsCompact (matrixNormBox F n ρ) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    Whittaker.JPSDilationAssembly.isCompact_le F.canonicalTopologicalData ρ

/-- The characteristic Schwartz test of the actual full-matrix norm box. -/
def matrixNormBoxTest (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) : MatrixTestFunction n F.Carrier :=
  Hecke.TestFunction.characteristic (isClopen_matrixNormBox F n hρ)
    (isCompact_matrixNormBox F n ρ)

theorem matrixNormBoxTest_diagonal_of_le (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (a : Fin (n + 1) → F.Carrierˣ) (ha : ∀ i, abv (a i : F.Carrier) ≤ ρ) :
    matrixNormBoxTest F n hρ (Iwasawa.diagonalUnits a).val = 1 := by
  rw [matrixNormBoxTest, Hecke.TestFunction.characteristic_apply]
  apply Set.indicator_of_mem
  intro i hi j hj
  rw [Iwasawa.diagonalUnits_val, Matrix.diagonal_apply]
  split_ifs with h
  · subst j
    exact ha i
  · change abv (0 : F.Carrier) ≤ ρ
    simpa only [map_zero] using hρ.le

/-- The positive rational weight supplied by the inverse upper-Borel
modulus and a slice-volume monomial. -/
def diagonalSliceWeight {n : ℕ} (e : Fin (n + 1) → ℕ)
    (a : Fin (n + 1) → F.Carrierˣ) : ℝ :=
  (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
    abv (a i : F.Carrier) / abv (a j : F.Carrier))⁻¹ *
      ∏ i, (abv (a i : F.Carrier))⁻¹ ^ e i

theorem diagonalSliceWeight_nonneg {n : ℕ} (e : Fin (n + 1) → ℕ)
    (a : Fin (n + 1) → F.Carrierˣ) : 0 ≤ diagonalSliceWeight F e a := by
  unfold diagonalSliceWeight
  exact mul_nonneg (inv_nonneg.mpr (Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun j _ => div_nonneg ((normalizedAbsoluteValue F.canonicalTopologicalData).nonneg _) ((normalizedAbsoluteValue F.canonicalTopologicalData).nonneg _)))
    (Finset.prod_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr ((normalizedAbsoluteValue F.canonicalTopologicalData).nonneg _)) _)

/-- The actual norm integrand with the geometric weight, cut off only by
a bounded diagonal box. -/
def boundedDiagonalNormIntegrand {n : ℕ} (e : Fin (n + 1) → ℕ) (ρ : ℝ)
    (s : ℂ) (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (a : Fin (n + 1) → F.Carrierˣ) : ℝ≥0∞ :=
  if ∀ i, abv (a i : F.Carrier) ≤ ρ then
    ENNReal.ofReal (diagonalSliceWeight F e a) *
      ‖f (Iwasawa.diagonalUnits a) * determinantWeight abv (Iwasawa.diagonalUnits a) s‖ₑ
  else 0

/-- The unchanged determinant weight splits off every nonnegative integral
power when its spectral exponent is lowered by that integer. -/
theorem enorm_weightedCoefficient_sub_natCast {n : ℕ}
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) (s : ℂ) (N : ℕ) :
    ‖f g * determinantWeight abv g s‖ₑ =
      ‖f g * determinantWeight abv g (s - (N : ℂ))‖ₑ *
        ENNReal.ofReal (abv (Matrix.det g.val) ^ N) := by
  have hne : (abv g.val.det : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ((normalizedAbsoluteValue F.canonicalTopologicalData).ne_zero g.det_ne_zero)
  have hsplit : determinantWeight abv g (s - (N : ℂ)) * (abv g.val.det : ℂ) ^ N =
      determinantWeight abv g s := by
    unfold determinantWeight
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hne, sub_add_cancel]
  rw [← hsplit, ← mul_assoc, enorm_mul, enorm_pow]
  congr 1
  rw [← ofReal_norm, Complex.norm_of_nonneg ((normalizedAbsoluteValue F.canonicalTopologicalData).nonneg _), ENNReal.ofReal_pow]
  exact (normalizedAbsoluteValue F.canonicalTopologicalData).nonneg _

/-- A fixed determinant shift reduces the full weighted box integrand to
one genuine matrix-test diagonal integrand. -/
theorem boundedDiagonalNormIntegrand_le_matrixDiagonal {n : ℕ}
    (e : Fin (n + 1) → ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      ∀ f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ,
      ∀ a : Fin (n + 1) → F.Carrierˣ,
        boundedDiagonalNormIntegrand F e ρ s f a ≤ ENNReal.ofReal C *
          ‖matrixDiagonalIntegrand F (matrixNormBoxTest F n hρ)
            (s - (diagonalWeightDegree n e : ℂ)) f a‖ₑ := by
  obtain ⟨C, hC, hbound⟩ := diagonalWeight_mul_det_pow_le n e ρ
  refine ⟨C, hC, fun s f a => ?_⟩
  unfold boundedDiagonalNormIntegrand
  split_ifs with ha
  · have hbox := matrixNormBoxTest_diagonal_of_le F n hρ a ha
    have hD : abv (Matrix.det (Iwasawa.diagonalUnits a).val) = ∏ i, abv (a i : F.Carrier) := by
      rw [Iwasawa.diagonalUnits_val, Matrix.det_diagonal, map_prod]
    have h := hbound (fun i => abv (a i : F.Carrier))
      (fun i => (normalizedAbsoluteValue F.canonicalTopologicalData).pos (a i).ne_zero) ha
    rw [enorm_weightedCoefficient_sub_natCast F f _ s (diagonalWeightDegree n e)]
    simp only [matrixDiagonalIntegrand, matrixIntegrand, hbox, one_mul]
    calc
      _ = ENNReal.ofReal (diagonalSliceWeight F e a *
          (∏ i, abv (a i : F.Carrier)) ^ diagonalWeightDegree n e) *
          ‖f (Iwasawa.diagonalUnits a) * determinantWeight abv (Iwasawa.diagonalUnits a)
            (s - (diagonalWeightDegree n e : ℂ))‖ₑ := by
        rw [hD, ENNReal.ofReal_mul (diagonalSliceWeight_nonneg F e a)]
        ring
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal h) le_rfl
  · exact zero_le

/-- Matrix convergence on one common right half-plane implies genuine
full-torus convergence of every such bounded diagonal geometric weight. -/
theorem boundedDiagonalNormIntegrand_convergesOnRight
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F σ)
    (e : Fin (n + 1) → ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ b : ℝ, ∀ f : biSmoothMatrixCoefficients σ, ∀ s : ℂ, b < s.re →
      ∫⁻ a, boundedDiagonalNormIntegrand F e ρ s f.val a
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) < ⊤ := by
  obtain ⟨b, hb⟩ := biSmooth_matrixDiagonal_convergesOnRight F σ hMatrix
  obtain ⟨C, hC, hbound⟩ := boundedDiagonalNormIntegrand_le_matrixDiagonal F e hρ
  let N : ℕ := diagonalWeightDegree n e
  refine ⟨b + (N : ℝ) + (jpssShift n).re, fun f s hs => ?_⟩
  have hs' : b < (s - (N : ℂ) - jpssShift n).re := by
    simp only [Complex.sub_re, Complex.natCast_re]
    linarith
  have hi := hb (matrixNormBoxTest F n hρ) f (s - (N : ℂ) - jpssShift n) hs'
  have hshift : s - (N : ℂ) - jpssShift n + jpssShift n = s - (N : ℂ) := by ring
  rw [hshift] at hi
  calc
    _ ≤ ∫⁻ a, ENNReal.ofReal C *
        ‖matrixDiagonalIntegrand F (matrixNormBoxTest F n hρ) (s - (N : ℂ)) f.val a‖ₑ
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) :=
      lintegral_mono (hbound s f.val)
    _ = ENNReal.ofReal C * ∫⁻ a,
        ‖matrixDiagonalIntegrand F (matrixNormBoxTest F n hρ) (s - (N : ℂ)) f.val a‖ₑ
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hasFiniteIntegral_iff_enorm.mp hi.hasFiniteIntegral)

end Langlands.RankinSelberg
