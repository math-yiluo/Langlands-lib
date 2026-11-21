import Langlands.Global.RankinSelberg.ComplexSquareFourierUnitaryAverage
import Langlands.Global.RankinSelberg.ComplexSquareZetaConvergence
import Langlands.Global.RankinSelberg.ComplexSquareZetaDualChange
import Langlands.Global.RankinSelberg.ComplexSquareZetaNormalization
import Langlands.Global.RankinSelberg.ComplexTateProductReversal
import Langlands.Global.RankinSelberg.ComplexTateProductScaledReflection
import Langlands.Global.RankinSelberg.ComplexTateProductStripGrowth

/-! # Functional equation for the complex square zeta integral of a standard vector -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator NNReal SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open ArchimedeanLocal
open Langlands.Archimedean Langlands.Archimedean.ComplexReverseTwist
open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ComplexGodement (upperTriangularEntries)
open ComplexSquareFourier
open ComplexTateProduct (reverseTest reverseTest_apply complexTateProductReversal
  IsEntireNormalization complexTateProductEntireFamily complexTateProductScaledReflection
  complexTateProductStripGrowth)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance squareReflectionGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance squareReflectionGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

variable {r : ℕ}
local notation "Rank" => r.succ
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "X" => UpperEntryPair (r + 1) → ℂ
local notation "Z" => Fin (r + 1) → ℂ

private abbrev dualVector (f : G → ℂ) : G → ℂ := fun g => f (inverseTranspose Rank ℂ g)

private theorem rightAverage_transform (κ : Measure K) [IsFiniteMeasure κ]
    (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ) (hf : Continuous f) (Y : Mat) :
    matrixTransform a (rightAverage κ (fun k => f k.val) (hf.comp continuous_subtype_val) Φ) Y =
      ∫ k : K, f k.val * matrixTransform a Φ (Y * (conjK Rank k).val.val) ∂κ := by
  let w (k : K) := f k.val
  have hw : Continuous w := hf.comp continuous_subtype_val
  let Ψ := rightAverage κ w hw Φ
  have hΨ (M : Mat) : Ψ M = ∫ k : K, w k * Φ ((1 : K).val.val * M * k.val.val) ∂κ := by
    change rightAverage κ w hw Φ M = _
    rw [rightAverage_apply]
    simp only [Subgroup.coe_one, Units.val_one, Matrix.one_mul]
  have h := complexSquareFourierUnitaryAverage κ a w (fun _ : K => (1 : K)) id
    hw continuous_const continuous_id Φ Ψ hΨ Y
  simpa only [map_one, Subgroup.coe_one, Units.val_one, Matrix.one_mul, id_eq] using h

private theorem dual_diagonalTest_of_average (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ) (hf : Continuous f)
    (hF : ∀ Y,
      matrixTransform a (rightAverage κ (fun k => f k.val) (hf.comp continuous_subtype_val) Φ) Y =
        ∫ k : K, f k.val * matrixTransform a Φ (Y * (conjK Rank k).val.val) ∂κ) :
    diagonalTest κ a (leftWeylTest (matrixTransform a Φ)) (twistLin Rank f)
        (hf.comp continuous_twist) =
      reverseTest (ComplexTraceFourier.transform a (diagonalTest κ a Φ f hf)) := by
  ext d
  rw [diagonalTest, upperMarginal_apply, reverseTest_apply]
  let Ψ := rightAverage κ (fun k => f k.val) (hf.comp continuous_subtype_val) Φ
  let F (z : X) := matrixTransform a Ψ ((upperTriangularEntries (d ∘ Fin.rev) z)ᵀ)
  let ν := Measure.pi (fun _ : UpperEntryPair Rank => (complexSelfDualMeasure a).measure)
  have : SigmaFinite (complexSelfDualMeasure a).measure := by
    rw [ComplexTraceFourier.measure_eq]
    infer_instance
  have hmp := measurePreserving_reverseOff (n := Rank) (complexSelfDualMeasure a).measure
  have htri : Continuous (upperTriangularEntries (d ∘ Fin.rev)) := by
    apply continuous_matrix
    intro i j
    by_cases h : i < j
    · simp only [upperTriangularEntries, dite_eq_left h]
      exact continuous_apply (⟨(i, j), h⟩ : UpperEntryPair Rank)
    · simp only [upperTriangularEntries, dite_eq_right h, continuous_const]
  have hcont : Continuous F := (matrixTransform a Ψ).continuous.comp htri.matrix_transpose
  calc
    _ = ∫ z : X, F (z ∘ reverseOff Rank) ∂ν := by
      apply integral_congr_ae
      filter_upwards with z
      rw [rightAverage_dual_change κ (matrixTransform a Φ) hf, w0_conjugate_triangular]
      exact (hF ((upperTriangularEntries (d ∘ Fin.rev) (z ∘ reverseOff Rank))ᵀ)).symm
    _ = ∫ z : X, F z ∂ν := by
      rw [← integral_map hmp.measurable.aemeasurable hcont.aestronglyMeasurable, hmp.map_eq]
    _ = _ := complexSquareFourierMarginal a Ψ (d ∘ Fin.rev)

/-- The entire normalized square zeta integrals of a complex standard vector and
its inverse-transpose dual satisfy Jacquet's reflection relation. -/
def ComplexSquareStandardFunctionalEquationStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (ds : Fin Rank → ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ),
    f ∈ complexStandardModule Rank (List.ofFn ds) →
    ∃ (σ : ℝ) (N Nd : ℂ → ℂ), Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
      (∀ s : ℂ, σ < s.re →
        Integrable (zetaKernel Φ f s) μ ∧
        Integrable (zetaKernel (matrixTransform a Φ) (dualVector f) s) μ ∧
        N s = (complexLFactor (List.ofFn ds)).denominator s * ∫ g, zetaKernel Φ f s g ∂μ ∧
        Nd s = (complexLFactor ((List.ofFn ds).map ComplexCharacterData.inv)).denominator s *
          ∫ g, zetaKernel (matrixTransform a Φ) (dualVector f) s g ∂μ) ∧
      ∀ s : ℂ, Nd (1 - s) =
        (complexEpsilon (List.ofFn ds) (-a) ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) * N s

private theorem squareConstantGrowth (c : ℂ) : HasStripExponentialGrowth (fun _ => c) :=
  fun _ _ => ⟨‖c‖, 0, 0, norm_nonneg _, le_rfl, fun _ _ _ _ => by simp⟩

/-- The same square functional equation with exponential growth on each vertical strip. -/
def ComplexSquareStandardFunctionalEquationGrowthStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (ds : Fin Rank → ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ),
    f ∈ complexStandardModule Rank (List.ofFn ds) →
    ∃ (σ : ℝ) (N Nd : ℂ → ℂ), Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
      HasStripExponentialGrowth N ∧ HasStripExponentialGrowth Nd ∧
      (∀ s : ℂ, σ < s.re →
        Integrable (zetaKernel Φ f s) μ ∧
        Integrable (zetaKernel (matrixTransform a Φ) (dualVector f) s) μ ∧
        N s = (complexLFactor (List.ofFn ds)).denominator s * ∫ g, zetaKernel Φ f s g ∂μ ∧
        Nd s = (complexLFactor ((List.ofFn ds).map ComplexCharacterData.inv)).denominator s *
          ∫ g, zetaKernel (matrixTransform a Φ) (dualVector f) s g ∂μ) ∧
      ∀ s : ℂ, Nd (1 - s) =
        (complexEpsilon (List.ofFn ds) (-a) ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) * N s

theorem complexSquareStandardFunctionalEquationGrowth :
    ComplexSquareStandardFunctionalEquationGrowthStatement (r := r) := by
  intro μ _ κ _ _ a ds Φ f hf
  obtain ⟨H, hH⟩ := complexTateProductEntireFamily r
  obtain ⟨c, _, hN⟩ := complexSquareZetaNormalization μ κ a H hH
  let dsD (j : Fin Rank) : ComplexCharacterData := (ds j.rev).inv
  let fD := twistLin Rank f
  let ΦD := leftWeylTest (matrixTransform a Φ)
  have hfD : fD ∈ complexStandardModule Rank (List.ofFn dsD) := twistLin_mem_standard_ofFn ds hf
  let T := diagonalTest κ a Φ f hf.1.continuous
  let Td := diagonalTest κ a ΦD fD hfD.1.continuous
  let m (j : Fin Rank) := (ds j).weight
  let md (j : Fin Rank) := (dsD j).weight
  let u (s : ℂ) (j : Fin Rank) := s + (ds j).exponent
  let ud (s : ℂ) (j : Fin Rank) := s + (dsD j).exponent
  let N (s : ℂ) := (c : ℂ) * H T m (u s)
  let Nd (s : ℂ) := (c : ℂ) * H Td md (ud s)
  obtain ⟨hNent, hNagree⟩ := hN ds Φ f hf
  obtain ⟨hNdent, hNdagree⟩ := hN dsD ΦD fD hfD
  obtain ⟨M, hC⟩ := complexSquareZetaConvergence (Nat.succ_pos r) ds
  obtain ⟨Md, hCd⟩ := complexSquareZetaConvergence (Nat.succ_pos r) dsD
  let q := (((Rank : ℂ) - 1) / 2).re
  let S : ℝ := ∑ j : Fin Rank, |(ds j).exponent.re|
  let σ := max ((Rank : ℝ) + M + Md + |q|) S
  have hGrowth (test : 𝓢(Z, ℂ)) (weight : Fin Rank → ℤ) (exponent : Z) :
      HasStripExponentialGrowth (fun s => (c : ℂ) * H test weight (fun j => s + exponent j)) := by
    have h := (squareConstantGrowth (c : ℂ)).mul
      (complexTateProductStripGrowth r H hH test weight exponent (fun _ => 1))
    change HasStripExponentialGrowth
      (fun s => (c : ℂ) * H test weight (ComplexTateProduct.affineParameter exponent (fun _ => 1) s)) at h
    have he (s : ℂ) : ComplexTateProduct.affineParameter exponent (fun _ => 1) s =
        fun j => s + exponent j := by
      funext j
      change exponent j + ((1 : ℝ) : ℂ) * s = s + exponent j
      rw [Complex.ofReal_one, one_mul, add_comm]
    simpa only [he] using h
  refine ⟨σ, N, Nd, hNent, hNdent, hGrowth T m _, hGrowth Td md _, ?_, ?_⟩
  · intro s hs
    have ht : ((Rank : ℝ) + M + Md + |q|) < s.re := (le_max_left _ _).trans_lt hs
    have hs0 : S < s.re := (le_max_right _ _).trans_lt hs
    have hpos (j : Fin Rank) : |(ds j).exponent.re| ≤ S :=
      Finset.single_le_sum (fun i _ => abs_nonneg (ds i).exponent.re) (Finset.mem_univ j)
    have hu (j : Fin Rank) : 0 < (u s j).re := by
      change 0 < s.re + (ds j).exponent.re
      linarith [hpos j, neg_abs_le (ds j).exponent.re]
    have hud (j : Fin Rank) : 0 < (ud s j).re := by
      change 0 < s.re + -(ds j.rev).exponent.re
      linarith [hpos j.rev, le_abs_self (ds j.rev).exponent.re]
    have hq : (s + ((Rank : ℂ) - 1) / 2).re = s.re + q := Complex.add_re _ _
    have hi := hC μ Φ f hf s (by rw [hq]; linarith [neg_abs_le q, (Nat.cast_nonneg Md : 0 ≤ (Md : ℝ))])
    have hid := hCd μ ΦD fD hfD s
      (by rw [hq]; linarith [neg_abs_le q, (Nat.cast_nonneg M : 0 ≤ (M : ℝ))])
    have hdual := complexSquareZetaDualChange μ (matrixTransform a Φ) f s
    refine ⟨hi, hdual.1.mpr hid, hNagree s hi hu, ?_⟩
    exact (hNdagree s hid hud).trans (by
      rw [denominator_complexLFactor_reverse_inv ds, hdual.2])
  · intro s
    have hT : Td = reverseTest (ComplexTraceFourier.transform a T) :=
      dual_diagonalTest_of_average κ a Φ f hf.1.continuous
        (rightAverage_transform κ a Φ f hf.1.continuous)
    have hm : md = (fun j => -m j) ∘ Fin.rev := by
      funext j
      exact ComplexCharacterData.inv_weight _
    have hu : ud (1 - s) = (fun j => 1 - u s j) ∘ Fin.rev := by
      funext j
      simp only [ud, dsD, ComplexCharacterData.inv_exponent, Function.comp_apply, u]
      ring
    have ht := complexTateProductScaledReflection r H hH a T m (u s)
    change H (ComplexTraceFourier.transform a T) (fun j => -m j) (fun j => 1 - u s j) =
      (∏ j, ((characterOfParams (ds j).weight 0).epsilon (-a) ‖(a : ℂ)‖₊
        (nnnorm_pos.mpr a.ne_zero) (s + (ds j).exponent) : ℂ)) * H T m (u s) at ht
    rw [epsilon_ofFn_shift] at ht
    change (c : ℂ) * H Td md (ud (1 - s)) = _ * ((c : ℂ) * H T m (u s))
    rw [hT, hm, hu, complexTateProductReversal H hH, ht]
    ring


theorem complexSquareStandardFunctionalEquation :
    ComplexSquareStandardFunctionalEquationStatement (r := r) := by
  intro μ _ κ _ _ a ds Φ f hf
  obtain ⟨σ, N, Nd, hN, hNd, _, _, hZ, hEq⟩ := complexSquareStandardFunctionalEquationGrowth μ κ a ds Φ f hf
  exact ⟨σ, N, Nd, hN, hNd, hZ, hEq⟩

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
