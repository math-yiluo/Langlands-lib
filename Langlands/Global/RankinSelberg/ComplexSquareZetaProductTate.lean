import Langlands.Analysis.SchwartzCompactAverage
import Langlands.Global.RankinSelberg.ComplexGodementAdditiveDiagonal
import Langlands.Global.RankinSelberg.ComplexSquareFourierMarginal
import Langlands.Global.RankinSelberg.ComplexSquareZetaPhase
import Langlands.Global.RankinSelberg.ComplexTateProductHolomorphy
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # Product Tate reduction of the complex square zeta integral -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator NNReal SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ComplexGodement (upperTriangularEntries integral_multiplicativeComplexDiagonal)
open ComplexSquareFourier (upperMarginal upperMarginal_apply)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance squareProductGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance squareProductGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance squareProductGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Z" => Fin n → ℂ
local notation "X" => UpperEntryPair n → ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

private abbrev rightAction (k : K) : Mat →L[ℝ] Mat :=
  (ContinuousLinearMap.mul ℝ Mat).flip k.val.val

private def rightInverseBound (n : ℕ) : ℝ :=
  max 1 (sSup (Set.range fun k : unitaryCompact ℂ n => ‖k.val⁻¹.val‖))

private theorem one_le_rightInverseBound : 1 ≤ rightInverseBound n := le_max_left _ _

private theorem norm_le_rightAction (M : Mat) (k : K) :
    ‖M‖ ≤ rightInverseBound n * ‖M * k.val.val‖ := by
  have hcont : Continuous (fun k : K => k.val⁻¹.val) :=
    Units.continuous_val.comp continuous_subtype_val.inv
  have hb := (isCompact_range hcont.norm).bddAbove
  have hinv : ‖k.val⁻¹.val‖ ≤ rightInverseBound n :=
    (le_csSup hb (Set.mem_range_self k)).trans (le_max_right _ _)
  calc
    ‖M‖ = ‖(M * k.val.val) * k.val⁻¹.val‖ := by
      rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    _ ≤ ‖M * k.val.val‖ * ‖k.val⁻¹.val‖ := norm_mul_le ..
    _ ≤ _ := by
      rw [mul_comm (rightInverseBound n)]
      exact mul_le_mul_of_nonneg_left hinv (norm_nonneg _)

/-- A weighted average of right unitary translates of a square Schwartz test. -/
def rightAverage (κ : Measure K) [IsFiniteMeasure κ] (w : K → ℂ) (hw : Continuous w)
    (Φ : 𝓢(Mat, ℂ)) : 𝓢(Mat, ℂ) :=
  Langlands.Analysis.SchwartzCompactAverage.average w rightAction Φ κ hw
    ((ContinuousLinearMap.mul ℝ Mat).flip.continuous.comp
      (Units.continuous_val.comp continuous_subtype_val))
    (zero_le_one.trans one_le_rightInverseBound) norm_le_rightAction

theorem rightAverage_apply (κ : Measure K) [IsFiniteMeasure κ] (w : K → ℂ) (hw : Continuous w)
    (Φ : 𝓢(Mat, ℂ)) (M : Mat) :
    rightAverage κ w hw Φ M = ∫ k, w k * Φ (M * k.val.val) ∂κ := rfl

private def upperExtraction : Mat →L[ℝ] X :=
  ({ toFun A := fun ij => A ij.1.1 ij.1.2
     map_add' _ _ := rfl
     map_smul' _ _ := rfl } : Mat →ₗ[ℝ] X).toContinuousLinearMap

private theorem upperExtraction_triangular (d : Z) (u : X) :
    upperExtraction (upperTriangularEntries d u) = u := by
  funext ij
  change upperTriangularEntries d u ij.1.1 ij.1.2 = u ij
  rw [upperTriangularEntries, dite_eq_left ij.2]

private theorem integrable_compactTriangular (κ : Measure K) [IsFiniteMeasure κ]
    (w : K → ℂ) (hw : Continuous w) (Φ : 𝓢(Mat, ℂ)) (d : Z) :
    Integrable (fun p : K × X => w p.1 * Φ (upperTriangularEntries d p.2 * p.1.val.val))
      (κ.prod (volume : Measure X)) := by
  let q := Module.finrank ℝ X + 1
  let A := max 1 ‖(upperExtraction (n := n))‖ * rightInverseBound n
  let C := 2 ^ q * ((Finset.Iic (q, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ
  obtain ⟨D, hD⟩ := (isCompact_univ.image hw.norm).bddAbove
  have hd (k : K) : ‖w k‖ ≤ max D 0 :=
    (hD ⟨k, Set.mem_univ k, rfl⟩).trans (le_max_left _ _)
  have htail : Integrable (fun z : X => (1 + ‖z‖) ^ (-(q : ℝ))) (volume : Measure X) :=
    integrable_one_add_norm (by dsimp [q]; exact_mod_cast Nat.lt_succ_self _)
  have ht : Continuous (upperTriangularEntries d) := by
    apply continuous_matrix
    intro i j
    by_cases h : i < j
    · simp only [upperTriangularEntries, dite_eq_left h]
      exact continuous_apply (⟨(i, j), h⟩ : UpperEntryPair n)
    · simp only [upperTriangularEntries, dite_eq_right h, continuous_const]
  refine ((htail.comp_snd κ).const_mul (max D 0 * (A ^ q * C))).mono' ?_ (ae_of_all _ fun p => ?_)
  · exact ((hw.comp continuous_fst).mul (Φ.continuous.comp ((ht.comp continuous_snd).matrix_mul
      (Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst))))).aestronglyMeasurable
  let B := upperTriangularEntries d p.2 * p.1.val.val
  have htri : ‖p.2‖ ≤ A * ‖B‖ := by
    calc
      ‖p.2‖ = ‖upperExtraction (upperTriangularEntries d p.2)‖ := by rw [upperExtraction_triangular]
      _ ≤ ‖upperExtraction‖ * ‖upperTriangularEntries d p.2‖ := upperExtraction.le_opNorm _
      _ ≤ max 1 ‖upperExtraction‖ * ‖upperTriangularEntries d p.2‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      _ ≤ _ := by
        dsimp only [A]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (norm_le_rightAction _ _) (zero_le_one.trans (le_max_left _ _))
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le (le_max_left _ _) one_le_rightInverseBound
  have hp : 1 + ‖p.2‖ ≤ A * (1 + ‖B‖) := by linarith [htri]
  have hΦ : (1 + ‖B‖) ^ q * ‖Φ B‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (q, 0)) le_rfl le_rfl Φ B
  have hΦ' : ‖Φ B‖ ≤ (A ^ q * C) * ((1 + ‖p.2‖) ^ q)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).2
    calc
      _ ≤ ‖Φ B‖ * (A * (1 + ‖B‖)) ^ q := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp _) (norm_nonneg _)
      _ = A ^ q * ((1 + ‖B‖) ^ q * ‖Φ B‖) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hΦ (by positivity)
  change ‖w p.1 * Φ B‖ ≤ max D 0 * (A ^ q * C) * (1 + ‖p.2‖) ^ (-(q : ℝ))
  rw [norm_mul, Real.rpow_neg (by positivity), Real.rpow_natCast, mul_assoc]
  exact mul_le_mul (hd p.1) hΦ' (norm_nonneg _) (le_max_right _ _)

private theorem upperMarginal_rightAverage (κ : Measure K) [IsFiniteMeasure κ]
    (w : K → ℂ) (hw : Continuous w) (Φ : 𝓢(Mat, ℂ)) (a : ℂˣ) (d : Z) :
    upperMarginal a (rightAverage κ w hw Φ) d =
      (ComplexTraceFourier.scale a ^ Fintype.card (UpperEntryPair n) : ℝ≥0) *
        (∫ k, (∫ z : X, Φ (upperTriangularEntries d z * k.val.val) * w k) ∂κ) := by
  rw [upperMarginal_apply, ComplexTraceFourier.product_measure_eq, integral_smul_nnreal_measure,
    NNReal.smul_def, Complex.real_smul]
  congr 1
  simp_rw [rightAverage_apply]
  let K₀ (p : K × X) := w p.1 * Φ (upperTriangularEntries d p.2 * p.1.val.val)
  have hI : Integrable K₀ (κ.prod (volume : Measure X)) := integrable_compactTriangular κ w hw Φ d
  change (∫ z : X, ∫ k, K₀ (k, z) ∂κ) = _
  rw [← integral_prod_symm _ hI, integral_prod _ hI]
  simp only [K₀, mul_comm (w _)]

private theorem density_mul_borelFactor (m : ℤ) (u z : ℂ) :
    (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * borelFactor m (2 * u) z =
      ComplexTateProduct.additiveWeight m u z := by
  by_cases hz : z = 0
  · simp [hz, ComplexTateProduct.additiveWeight]
  rw [borelFactor_eq_cpow _ _ hz, ComplexTateProduct.additiveWeight, ite_eq_right hz,
    Complex.ofReal_inv, Complex.ofReal_pow, ← Complex.cpow_ofNat _ 2, ← Complex.cpow_neg,
    mul_left_comm, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))]
  rw [show -(2 : ℂ) + 2 * u = 2 * u - 2 by ring]

/-- The square zeta integral of a standard vector equals the diagonal product Tate integral
of the upper marginal of its weighted compact Schwartz average. -/
def ComplexSquareZetaProductTateStatement : Prop :=
  ∀ (μ : Measure G) (κ : Measure K) [IsFiniteMeasure κ] (a : ℂˣ),
    μ.IsHaarMeasure → κ.IsHaarMeasure →
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (ds : Fin n → ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ)
      (hf : f ∈ complexStandardModule n (List.ofFn ds)) (s : ℂ),
      Integrable (zetaKernel Φ f s) μ →
      let w (k : K) := f k.val
      let h : Continuous w := hf.1.continuous.comp continuous_subtype_val
      (∫ g, zetaKernel Φ f s g ∂μ) = (c : ℂ) *
        ComplexTateProduct.zeta (upperMarginal a (rightAverage κ w h Φ))
          (fun j => (ds j).weight) (fun j => s + (ds j).exponent)

theorem complexSquareZetaProductTate : ComplexSquareZetaProductTateStatement (n := n) := by
  intro μ κ hκfinite a hμ hκ
  obtain ⟨c, hc, hphase⟩ := complexSquareZetaPhase μ κ hμ hκ
  let Q := ComplexTraceFourier.scale a ^ Fintype.card (UpperEntryPair n)
  have hQ : 0 < Q := pow_pos (ComplexTraceFourier.scale_pos a) _
  refine ⟨c / Q, div_pos hc hQ, fun ds Φ f hf s hI => ?_⟩
  dsimp only
  let w (k : K) := f k.val
  let hw : Continuous w := hf.1.continuous.comp continuous_subtype_val
  let Ψ := upperMarginal a (rightAverage κ w hw Φ)
  let B (d : Z) := ∫ k, ∫ z : X, multiplicativeKernel ds Φ f s d k z ∂volume ∂κ
  let D (d : Z) : ℝ := ∏ j, (‖d j‖ ^ 2)⁻¹
  have hT : (Q : ℂ) * (∫ d, D d • B d) =
      ComplexTateProduct.zeta Ψ (fun j => (ds j).weight) (fun j => s + (ds j).exponent) := by
    rw [← integral_const_mul, ComplexTateProduct.zeta]
    apply integral_congr_ae
    filter_upwards with d
    rw [ComplexTateProduct.integrand]
    have hm := upperMarginal_rightAverage κ w hw Φ a d
    change Ψ d = _ at hm
    rw [hm, Complex.real_smul]
    have hweight : (D d : ℂ) *
        (∏ j, borelFactor (ds j).weight (2 * (s + (ds j).exponent)) (d j)) =
      ∏ j, ComplexTateProduct.additiveWeight (ds j).weight (s + (ds j).exponent) (d j) := by
      dsimp only [D]
      rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => density_mul_borelFactor _ _ _
    simp only [B, multiplicativeKernel, integral_mul_const, ← hweight, w]
    ring
  rw [hphase ds Φ f Φ.continuous hf s hI, integral_multiplicativeComplexDiagonal]
  change (c : ℂ) * (∫ d, D d • B d) = ((c / Q : ℝ≥0) : ℂ) *
    ComplexTateProduct.zeta Ψ (fun j => (ds j).weight) (fun j => s + (ds j).exponent)
  rw [← hT, NNReal.coe_div, Complex.ofReal_div]
  field_simp [show (Q : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr hQ).ne']

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
