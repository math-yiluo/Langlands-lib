import Langlands.Analysis.SchwartzPartialFourierBound
import Langlands.Global.RankinSelberg.ComplexGodementAddedCharacter
import Langlands.Global.RankinSelberg.ComplexGodementWhittakerFamily

/-! # Uniform Schwartz estimates for translated Godement tests -/

noncomputable section

open MeasureTheory Set
open scoped Classical ContDiff Matrix.Norms.Elementwise NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementTranslatedBounds

open Langlands.Analysis.SchwartzPartialFourier (exists_bound_transform_pullback)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open ComplexGodementAddedCharacter (rightTest)
open ComplexGodementColumnChange (iteratedKernel iteratedKernel_eq)
open ComplexGodementPartialFourier (partialSchwartz partialSchwartz_apply)
open ComplexGodementWhittaker (augmentedPoint continuous_augmentedPoint detLog kernelBase)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound exists_integrable_majorant testSeminorm)
open ArchimedeanLocal (complexNormalizedAbs)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "Square" => Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ

/-- A common upper bound for the operator norms of matrix right multiplication and its inverse
on the rectangular matrix space with its entrywise supremum norm. -/
def rightTestSize (g : G') : ℝ := max 1 ((r + 1 + 1 : ℕ) * max ‖g.val‖ ‖g⁻¹.val‖)

theorem one_le_rightTestSize (g : G') : 1 ≤ rightTestSize g := le_max_left _ _

theorem continuous_rightTestSize : Continuous (rightTestSize (r := r)) :=
  continuous_const.max ((Units.continuous_val.norm.max
    (Units.continuous_val.comp continuous_inv).norm).const_mul _)

private theorem norm_rightMul_le (X : Rect) (Y : Square) :
    ‖X * Y‖ ≤ (r + 1 + 1 : ℕ) * ‖X‖ * ‖Y‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k : Fin (r + 1 + 1), ‖X i k * Y k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin (r + 1 + 1), ‖X‖ * ‖Y‖ := by
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm X)
        (Matrix.norm_entry_le_entrywise_sup_norm Y) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

private theorem seminorm_pullback_le (A : Rect ≃L[ℝ] Rect) (R : ℝ) (hR : 0 ≤ R)
    (hA : ‖A.toContinuousLinearMap‖ ≤ R) (hI : ‖A.symm.toContinuousLinearMap‖ ≤ R)
    (k n : ℕ) (Φ : 𝓢(Rect, ℂ)) :
    SchwartzMap.seminorm ℝ k n (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A Φ) ≤
      R ^ (k + n) * SchwartzMap.seminorm ℝ k n Φ := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro X
  have hx : ‖X‖ ≤ R * ‖A X‖ := by
    calc
      ‖X‖ = ‖A.symm (A X)‖ := by rw [A.symm_apply_apply]
      _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖A X‖ := A.symm.toContinuousLinearMap.le_opNorm (A X)
      _ ≤ _ := mul_le_mul_of_nonneg_right hI (norm_nonneg _)
  change ‖X‖ ^ k * ‖iteratedFDeriv ℝ n (Φ ∘ A.toContinuousLinearMap) X‖ ≤ _
  rw [A.toContinuousLinearMap.iteratedFDeriv_comp_right (Φ.smooth ⊤) X (by simp)]
  have hb := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n Φ (A X)) (fun _ => A.toContinuousLinearMap)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  have hn := hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hA n) (norm_nonneg _))
  calc
    _ ≤ (R * ‖A X‖) ^ k * (‖iteratedFDeriv ℝ n Φ (A X)‖ * R ^ n) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx k) hn (norm_nonneg _) (by positivity)
    _ = R ^ (k + n) * (‖A X‖ ^ k * ‖iteratedFDeriv ℝ n Φ (A X)‖) := by
      rw [mul_pow, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Φ.le_seminorm ℝ k n (A X)) (by positivity)

/-- Right pullback costs only a fixed power of the group size in each Schwartz seminorm. -/
theorem seminorm_rightTest_le (k n : ℕ) (g : G') (Φ : 𝓢(Rect, ℂ)) :
    SchwartzMap.seminorm ℝ k n (rightTest g Φ) ≤
      rightTestSize g ^ (k + n) * SchwartzMap.seminorm ℝ k n Φ := by
  have hR := zero_le_one.trans (one_le_rightTestSize g)
  unfold rightTest
  apply seminorm_pullback_le _ _ hR
  · apply ContinuousLinearMap.opNorm_le_bound _ hR
    intro X
    change ‖X * g.val‖ ≤ _
    exact (norm_rightMul_le X g.val).trans (by
      rw [mul_right_comm]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)).trans (le_max_right _ _))
  · apply ContinuousLinearMap.opNorm_le_bound _ hR
    intro X
    change ‖X * g⁻¹.val‖ ≤ _
    exact (norm_rightMul_le X g⁻¹.val).trans (by
      rw [mul_right_comm]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)).trans (le_max_right _ _))

private theorem continuous_kernel (d : ComplexCharacterData) (W : G → ℂ) (hW : Continuous W)
    (Φ : 𝓢(Rect, ℂ)) (s : ℂ) :
    Continuous (fun h => kernelBase d Φ W h * ArchimedeanLocal.detPower complexNormalizedAbs h s) := by
  have hd : Continuous (fun h : G => h.val.det) := Units.continuous_val.matrix_det
  have hl : Continuous (detLog (r := r)) := (hd.norm.pow 2).log fun h =>
    (pow_pos (norm_pos_iff.mpr h.det_ne_zero) 2).ne'
  have hχ : Continuous (fun h : G => (d.character (Langlands.GeneralLinear.determinant h) : ℂ)) :=
    Units.continuous_val.comp (d.character.continuous.comp Langlands.GeneralLinear.determinantContinuous.continuous)
  exact (((Φ.continuous.comp continuous_augmentedPoint).mul (hW.comp continuous_inv)).mul hχ).mul
    ((Complex.continuous_ofReal.comp hl).const_mul s).cexp

variable (r) in
/-- On a bounded real spectral range with uniform smaller Whittaker estimates, the outer
Godement integral of any right-translated Schwartz test is absolutely convergent and is
controlled by finitely many seminorms of the original test times a fixed power of the group size. -/
def ComplexGodementTranslatedBoundsStatement : Prop :=
  ∀ {P : Type} (ν : Measure G) [ν.IsHaarMeasure] (μ : AdditiveHaarMeasure ℂ)
    (a : ℂˣ) (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ),
      (∀ p ∈ S, Continuous (W p)) → HasUniformSimpleRootBound S W →
      ∀ T : ℝ, 0 ≤ T →
        ∃ (I : Finset (ℕ × ℕ)) (N : ℕ) (B : G → ℝ), Integrable B ν ∧ (∀ h, 0 ≤ B h) ∧
          ∀ p ∈ S, ∀ s : ℂ, |(s - 1).re| ≤ T → ∀ (g : G') (Φ : 𝓢(Rect, ℂ)),
            let K := iteratedKernel (complexScaledCharacter a) μ d (rightTest g Φ) (W p) s
            Integrable K ν ∧
              (∀ h, ‖K h‖ ≤ B h * rightTestSize g ^ N * I.sup (schwartzSeminormFamily ℝ Rect ℂ) Φ) ∧
              ‖∫ h, K h ∂ν‖ ≤ (∫ h, B h ∂ν) * rightTestSize g ^ N * I.sup (schwartzSeminormFamily ℝ Rect ℂ) Φ

set_option maxHeartbeats 900000 in
theorem complexGodementTranslatedBounds : ComplexGodementTranslatedBoundsStatement r := by
  intro P ν hν μ a d S W hWc hWb T hT
  obtain ⟨j, B, hBi, hB⟩ := exists_integrable_majorant ν S W hWb d T hT
  have hb : ∃ q : Seminorm ℝ 𝓢(Rect, ℂ), Continuous q ∧
      ∀ Φ : 𝓢(Rect, ℂ), testSeminorm j (partialSchwartz a μ Φ) ≤ q Φ := by
    unfold partialSchwartz
    exact exists_bound_transform_pullback _ _ _ j
  obtain ⟨q, hq, hb⟩ := hb
  obtain ⟨I, c, _, hc⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ Rect ℂ) q hq
  let N := I.sup (fun z => z.1 + z.2)
  let D : G → ℝ := fun h => (c : ℝ) * ‖B h‖
  have hB₀ : 0 ≤ ∫ h, ‖B h‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  refine ⟨I, N, D, hBi.norm.const_mul _, fun h => by dsimp only [D]; positivity,
    fun p hp s hs g Φ => ?_⟩
  let Ψ := rightTest g Φ
  let X := partialSchwartz a μ Ψ
  let F := iteratedKernel (complexScaledCharacter a) μ d Ψ (W p) s
  have hF (h : G) :
      F h = kernelBase d X (W p) h * ArchimedeanLocal.detPower complexNormalizedAbs h (s - 1) :=
    iteratedKernel_eq (complexScaledCharacter a) μ d Ψ X (partialSchwartz_apply a μ Ψ) (W p) s h
  have hFn (h : G) : ‖F h‖ ≤ q Ψ * ‖B h‖ := by
    rw [hF, Real.norm_eq_abs]
    exact (hB p hp (s - 1) hs X h).trans
      ((mul_le_mul_of_nonneg_left (le_abs_self (B h)) (apply_nonneg _ _)).trans
        (mul_le_mul_of_nonneg_right (hb Ψ) (abs_nonneg _)))
  have hFc : Continuous F := by
    rw [show F = _ from funext hF]
    exact continuous_kernel d (W p) (hWc p hp) X (s - 1)
  have hFi : Integrable F ν :=
    (hBi.norm.const_mul (q Ψ)).mono' hFc.aestronglyMeasurable (ae_of_all _ hFn)
  have hR := zero_le_one.trans (one_le_rightTestSize g)
  have hRq : q Ψ ≤ (c : ℝ) * (rightTestSize g ^ N * I.sup (schwartzSeminormFamily ℝ Rect ℂ) Φ) := by
    refine (hc Ψ).trans (mul_le_mul_of_nonneg_left ?_ c.coe_nonneg)
    apply Seminorm.finset_sup_apply_le (mul_nonneg (pow_nonneg hR _) (apply_nonneg _ _))
    intro i hi
    have hiN : i.1 + i.2 ≤ N := Finset.le_sup (f := fun z => z.1 + z.2) hi
    refine (seminorm_rightTest_le i.1 i.2 g Φ).trans ?_
    exact mul_le_mul (pow_le_pow_right₀ (one_le_rightTestSize g) hiN)
      (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ Rect ℂ) (x := Φ) hi)
      (apply_nonneg _ _) (pow_nonneg hR _)
  refine ⟨hFi, fun h => ?_, ?_⟩
  · change ‖F h‖ ≤ _
    exact (hFn h).trans ((mul_le_mul_of_nonneg_right hRq (norm_nonneg _)).trans_eq (by dsimp only [D]; ring))
  · change ‖∫ h, F h ∂ν‖ ≤ (∫ h, (c : ℝ) * ‖B h‖ ∂ν) * rightTestSize g ^ N * _
    rw [integral_const_mul]
    calc
      _ ≤ ∫ h, ‖F h‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ h, q Ψ * ‖B h‖ ∂ν := integral_mono hFi.norm (hBi.norm.const_mul _) hFn
      _ = q Ψ * ∫ h, ‖B h‖ ∂ν := integral_const_mul _ _
      _ ≤ _ := (mul_le_mul_of_nonneg_right hRq hB₀).trans_eq (by ring)

end Langlands.Global.RankinSelbergGlobal.ComplexGodementTranslatedBounds
