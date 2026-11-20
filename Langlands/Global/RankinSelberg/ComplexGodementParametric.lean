import Langlands.Global.RankinSelberg.ComplexGodementTranslatedBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! # Group continuity and directional differentiation of the Godement continuation -/

noncomputable section

open MeasureTheory Set Filter
open scoped Classical ContDiff Matrix.Norms.Elementwise SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementParametric

open Langlands.Analysis.SchwartzPartialFourier (valueSeminorm)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure UnitaryAdditiveCharacter rowMeasure rowPairing
  rectangularFirstColumns rectangularLastColumn rectangularJoin rectangularJoin_last continuous_rectangularJoin)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open ComplexGodement (characterWeight continuous_characterWeight)
open ComplexGodementAddedCharacter (rightTest rightTest_apply continuedValue)
open ComplexGodementColumnChange (iteratedKernel iteratedKernel_eq)
open ComplexGodementPartialFourier (partialSchwartz partialSchwartz_apply)
open ComplexGodementTranslatedBounds (rightTestSize one_le_rightTestSize continuous_rightTestSize
  seminorm_rightTest_le complexGodementTranslatedBounds)
open ComplexGodementWhittaker (augmentedPoint kernelBase)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ArchimedeanLocal (complexNormalizedAbs)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Square" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Col" => Fin (r + 1) → ℂ

local notation "q" => (Module.finrank ℝ Col + 1)

private def columnTail (y : Col) : ℝ := ((1 + ‖y‖) ^ q)⁻¹

private theorem integrable_columnTail (μ : AdditiveHaarMeasure ℂ) : Integrable (columnTail (r := r)) (rowMeasure μ (r + 1)) := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have hq : (Module.finrank ℝ Col : ℝ) < (q : ℕ) := by
    exact_mod_cast Nat.lt_succ_self (Module.finrank ℝ Col)
  refine (integrable_one_add_norm (μ := rowMeasure μ (r + 1)) hq).congr (ae_of_all _ fun y => ?_)
  simp only [columnTail, Real.rpow_neg (show 0 ≤ 1 + ‖y‖ by positivity), Real.rpow_natCast]

private theorem valueSeminorm_rightTest_le (j : ℕ) (Φ : 𝓢(Rect, ℂ)) (g : G') {R : ℝ}
    (hR : rightTestSize g ≤ R) : valueSeminorm j (rightTest g Φ) ≤ R ^ j * valueSeminorm j Φ := by
  have h₁ := (one_le_rightTestSize g).trans hR
  have h₀ := zero_le_one.trans h₁
  apply Seminorm.finset_sup_apply_le (mul_nonneg (pow_nonneg h₀ _) (apply_nonneg _ _))
  rintro ⟨i, n⟩ hi
  obtain ⟨hk, hn⟩ := Finset.mem_Iic.mp hi
  have hn₀ : n = 0 := Nat.eq_zero_of_le_zero hn
  subst n
  have hpower : rightTestSize g ^ (i + 0) ≤ R ^ j :=
    (pow_le_pow_left₀ (zero_le_one.trans (one_le_rightTestSize g)) hR _).trans
      (pow_le_pow_right₀ h₁ (by simpa only [Nat.add_zero] using hk))
  exact (seminorm_rightTest_le i 0 g Φ).trans (mul_le_mul hpower
    (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ Rect ℂ) (x := Φ) hi)
    (apply_nonneg _ _) (pow_nonneg h₀ _))

private def columnIntegrand (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (X : Rect) (g : G') (y : Col) : ℂ :=
  rightTest g Φ (rectangularJoin (rectangularFirstColumns X) y) *
    (complexScaledCharacter a).complex (rowPairing (rectangularLastColumn X) y)

private theorem partialSchwartz_eq_integral (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (Φ : 𝓢(Rect, ℂ)) (X : Rect) (g : G') :
    partialSchwartz a μ (rightTest g Φ) X = ∫ y, columnIntegrand a Φ X g y ∂rowMeasure μ (r + 1) :=
  partialSchwartz_apply a μ (rightTest g Φ) X

private theorem norm_columnIntegrand_le (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (X : Rect) (g : G')
    {R : ℝ} (hR : rightTestSize g ≤ R) (y : Col) :
    ‖columnIntegrand a Φ X g y‖ ≤ (2 ^ q * (R ^ q * valueSeminorm q Φ)) * columnTail y := by
  let A := rectangularJoin (rectangularFirstColumns X) y
  have hy : ‖y‖ ≤ ‖A‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    rw [← rectangularJoin_last (rectangularFirstColumns X) y i]
    exact Matrix.norm_entry_le_entrywise_sup_norm A
  have hΦ := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (q, 0))
    le_rfl le_rfl (rightTest g Φ) A
  rw [norm_iteratedFDeriv_zero] at hΦ
  rw [columnIntegrand, norm_mul, UnitaryAdditiveCharacter.norm_complex, mul_one,
    columnTail, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).2
  calc
    _ ≤ ‖rightTest g Φ A‖ * (1 + ‖A‖) ^ q := by gcongr
    _ ≤ 2 ^ q * valueSeminorm q (rightTest g Φ) := by rw [mul_comm]; exact hΦ
    _ ≤ _ := mul_le_mul_of_nonneg_left (valueSeminorm_rightTest_le q Φ g hR) (by positivity)

private theorem continuous_columnIntegrand (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (X : Rect) (g : G') :
    Continuous (columnIntegrand a Φ X g) := by
  have hjoin : Continuous (fun y : Col => rectangularJoin (rectangularFirstColumns X) y) :=
    continuous_rectangularJoin.comp (continuous_const.prodMk continuous_id)
  have hp : Continuous (fun y : Col => rowPairing (rectangularLastColumn X) y) := by
    unfold rowPairing
    exact continuous_finsetSum _ fun i _ => ((continuous_apply i) : Continuous (fun y : Col => y i)).const_mul _
  exact ((rightTest g Φ).continuous.comp hjoin).mul ((complexScaledCharacter a).continuous_complex.comp hp)

private theorem integrable_columnIntegrand (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (Φ : 𝓢(Rect, ℂ)) (X : Rect) (g : G') : Integrable (columnIntegrand a Φ X g) (rowMeasure μ (r + 1)) :=
  ((integrable_columnTail μ).const_mul (2 ^ q * (rightTestSize g ^ q * valueSeminorm q Φ))).mono'
    (continuous_columnIntegrand a Φ X g).aestronglyMeasurable
    (ae_of_all _ fun y => norm_columnIntegrand_le a Φ X g le_rfl y)

private theorem continuous_partialSchwartz_rightTest (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (Φ : 𝓢(Rect, ℂ)) (X : Rect) : Continuous (fun g : G' => partialSchwartz a μ (rightTest g Φ) X) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  simp_rw [partialSchwartz_eq_integral μ a Φ X]
  let R := rightTestSize g₀ + 1
  have hR : ∀ᶠ g in 𝓝 g₀, rightTestSize g < R :=
    continuous_rightTestSize.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
  apply continuousAt_of_dominated (bound := fun y => (2 ^ q * (R ^ q * valueSeminorm q Φ)) * columnTail y)
  · exact Eventually.of_forall fun g => (continuous_columnIntegrand a Φ X g).aestronglyMeasurable
  · exact hR.mono fun g hg => ae_of_all _ fun y => norm_columnIntegrand_le a Φ X g hg.le y
  · exact (integrable_columnTail μ).const_mul _
  · refine ae_of_all _ fun y => Continuous.continuousAt ?_
    exact (Φ.continuous.comp (continuous_const.matrix_mul Units.continuous_val)).mul continuous_const

/-- The directional derivative of a Schwartz test along a linear vector field. -/
def directionalTest (A : Rect →L[ℝ] Rect) : 𝓢(Rect, ℂ) →L[ℝ] 𝓢(Rect, ℂ) :=
  (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℝ ℂ).flip A.hasTemperateGrowth).comp
    (SchwartzMap.fderivCLM ℝ Rect ℂ)

@[simp]
theorem directionalTest_apply (A : Rect →L[ℝ] Rect) (Φ : 𝓢(Rect, ℂ)) (X : Rect) :
    directionalTest A Φ X = fderiv ℝ Φ X (A X) := rfl

private theorem hasDerivAt_partialSchwartz_curve (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (Φ : 𝓢(Rect, ℂ)) (X : Rect) (γ : ℝ → G') (hγ : Continuous γ) (A : Rect →L[ℝ] Rect)
    (hD : ∀ (t : ℝ) (Y : Rect), HasDerivAt (fun v => Y * (γ v).val) (A (Y * (γ t).val)) t) (t₀ : ℝ) :
    HasDerivAt (fun t => partialSchwartz a μ (rightTest (γ t) Φ) X)
      (partialSchwartz a μ (rightTest (γ t₀) (directionalTest A Φ)) X) t₀ := by
  let K (t : ℝ) := columnIntegrand a Φ X (γ t)
  let Ψ := directionalTest A Φ
  let K' (t : ℝ) := columnIntegrand a Ψ X (γ t)
  let R := rightTestSize (γ t₀) + 1
  let S : Set ℝ := {t | rightTestSize (γ t) < R}
  have hS : S ∈ 𝓝 t₀ := ((continuous_rightTestSize.comp hγ).continuousAt.eventually_lt
    continuousAt_const (lt_add_one _))
  have hDeriv (y : Col) (t : ℝ) : HasDerivAt (fun v => K v y) (K' t y) t := by
    let Y := rectangularJoin (rectangularFirstColumns X) y
    have hΦ := (Φ.hasFDerivAt (Y * (γ t).val)).comp_hasDerivAt t (hD t Y)
    simpa only [K, K', columnIntegrand, rightTest_apply, Ψ, directionalTest_apply, Function.comp_def, Y] using hΦ.mul_const
      ((complexScaledCharacter a).complex (rowPairing (rectangularLastColumn X) y))
  simp_rw [partialSchwartz_eq_integral]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := K) (F' := K') (s := S)
    (bound := fun y => (2 ^ q * (R ^ q * valueSeminorm q Ψ)) * columnTail y)
    hS (Eventually.of_forall fun t => (continuous_columnIntegrand a Φ X (γ t)).aestronglyMeasurable)
    (integrable_columnIntegrand μ a Φ X (γ t₀)) (continuous_columnIntegrand a Ψ X (γ t₀)).aestronglyMeasurable
    (ae_of_all _ fun y t ht => norm_columnIntegrand_le a Ψ X (γ t) (show _ < R from ht).le y)
    ((integrable_columnTail μ).const_mul _) (ae_of_all _ fun y t _ => hDeriv y t)).2

private theorem continuous_iteratedKernel_rightTest (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (W : G → ℂ) (s : ℂ) (h : G) :
    Continuous (fun g : G' => iteratedKernel (complexScaledCharacter a) μ d (rightTest g Φ) W s h) := by
  have he (g : G') : iteratedKernel (complexScaledCharacter a) μ d (rightTest g Φ) W s h =
      kernelBase d (partialSchwartz a μ (rightTest g Φ)) W h * ArchimedeanLocal.detPower complexNormalizedAbs h (s - 1) :=
    iteratedKernel_eq _ _ _ _ _ (partialSchwartz_apply a μ (rightTest g Φ)) _ _ _
  simp_rw [he, kernelBase]
  exact (((continuous_partialSchwartz_rightTest μ a Φ (augmentedPoint h)).mul_const _).mul_const _).mul_const _

/-- Under uniform smaller-rank estimates the continued Godement value is continuous in the
larger group argument at every fixed parameter. -/
theorem continuous_continuedValue {P : Type} (ν : Measure G) [ν.IsHaarMeasure]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ)
    (hWc : ∀ p ∈ S, Continuous (W p)) (hWb : HasUniformSimpleRootBound S W)
    (p : P) (hp : p ∈ S) (Φ : 𝓢(Rect, ℂ)) (s : ℂ) :
    Continuous (fun g : G' => continuedValue ν μ d a Φ (W p) g s) := by
  let t : ℂ := (((r + 1 : ℕ) + 1 : ℂ) / 2) + s
  let K (g : G') := iteratedKernel (complexScaledCharacter a) μ d (rightTest g Φ) (W p) t
  obtain ⟨I, N, B, hBi, hB₀, hb⟩ :=
    complexGodementTranslatedBounds ν μ a d S W hWc hWb |(t - 1).re| (abs_nonneg _)
  have hI : Continuous (fun g : G' => ∫ h, K g h ∂ν) := by
    rw [continuous_iff_continuousAt]
    intro g₀
    let R := rightTestSize g₀ + 1
    have hR : ∀ᶠ g in 𝓝 g₀, rightTestSize g < R :=
      continuous_rightTestSize.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
    let C := I.sup (schwartzSeminormFamily ℝ Rect ℂ) Φ
    apply continuousAt_of_dominated (bound := fun h => B h * (R ^ N * C))
    · exact Eventually.of_forall fun g => (hb p hp t le_rfl g Φ).1.aestronglyMeasurable
    · exact hR.mono fun g hg => ae_of_all _ fun h => ((hb p hp t le_rfl g Φ).2.1 h).trans (by
        rw [mul_assoc]
        have hg₀ := zero_le_one.trans (one_le_rightTestSize g)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hg₀ hg.le _) (apply_nonneg _ _)) (hB₀ h))
    · exact hBi.mul_const _
    · exact ae_of_all _ fun h => (continuous_iteratedKernel_rightTest μ a d Φ (W p) t h).continuousAt
  have hdet : Continuous (Langlands.GeneralLinear.determinant : G' → ℂˣ) :=
    Langlands.GeneralLinear.determinantContinuous.continuous
  have hlog : Continuous (fun g : G' => Real.log (complexNormalizedAbs g.val.det)) :=
    (Units.continuous_val.matrix_det.norm.pow 2).log fun g =>
      (pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)) 2).ne'
  have he : Continuous (fun g : G' => ArchimedeanLocal.detPower complexNormalizedAbs g s) :=
    ((Complex.continuous_ofReal.comp hlog).const_mul s).cexp
  exact ((((continuous_characterWeight d _).comp hdet).const_mul _).mul he).mul hI

/-- Along a smooth translation curve with a fixed linear vector field on the test matrices,
differentiation of the outer Godement integral differentiates the test before translation. -/
theorem hasDerivAt_integral_iteratedKernel_curve {P : Type} (ν : Measure G) [ν.IsHaarMeasure]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ)
    (hWc : ∀ p ∈ S, Continuous (W p)) (hWb : HasUniformSimpleRootBound S W)
    (p : P) (hp : p ∈ S) (Φ : 𝓢(Rect, ℂ)) (s : ℂ) (γ : ℝ → G') (hγ : Continuous γ) (A : Rect →L[ℝ] Rect)
    (hD : ∀ (t : ℝ) (Y : Rect), HasDerivAt (fun v => Y * (γ v).val) (A (Y * (γ t).val)) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ h, iteratedKernel (complexScaledCharacter a) μ d (rightTest (γ t) Φ) (W p) s h ∂ν)
      (∫ h, iteratedKernel (complexScaledCharacter a) μ d (rightTest (γ t₀) (directionalTest A Φ)) (W p) s h ∂ν) t₀ := by
  let Ψ := directionalTest A Φ
  let K (t : ℝ) := iteratedKernel (complexScaledCharacter a) μ d (rightTest (γ t) Φ) (W p) s
  let K' (t : ℝ) := iteratedKernel (complexScaledCharacter a) μ d (rightTest (γ t) Ψ) (W p) s
  obtain ⟨I, N, B, hBi, hB₀, hb⟩ :=
    complexGodementTranslatedBounds ν μ a d S W hWc hWb |(s - 1).re| (abs_nonneg _)
  let R := rightTestSize (γ t₀) + 1
  let U : Set ℝ := {t | rightTestSize (γ t) < R}
  have hU : U ∈ 𝓝 t₀ := (continuous_rightTestSize.comp hγ).continuousAt.eventually_lt
    continuousAt_const (lt_add_one _)
  have hDeriv (t : ℝ) (h : G) : HasDerivAt (fun v => K v h) (K' t h) t := by
    have he (f : 𝓢(Rect, ℂ)) (v : ℝ) : iteratedKernel (complexScaledCharacter a) μ d (rightTest (γ v) f) (W p) s h =
        kernelBase d (partialSchwartz a μ (rightTest (γ v) f)) (W p) h *
          ArchimedeanLocal.detPower complexNormalizedAbs h (s - 1) :=
      iteratedKernel_eq _ _ _ _ _ (partialSchwartz_apply a μ (rightTest (γ v) f)) _ _ _
    simp only [K, K', he, kernelBase]
    exact (((hasDerivAt_partialSchwartz_curve μ a Φ (augmentedPoint h) γ hγ A hD t).mul_const _).mul_const _).mul_const _
  let C := I.sup (schwartzSeminormFamily ℝ Rect ℂ) Ψ
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := K) (F' := K') (s := U)
    (bound := fun h => B h * (R ^ N * C)) hU
    (Eventually.of_forall fun t => (hb p hp s le_rfl (γ t) Φ).1.aestronglyMeasurable)
    (hb p hp s le_rfl (γ t₀) Φ).1 (hb p hp s le_rfl (γ t₀) Ψ).1.aestronglyMeasurable
    (ae_of_all _ fun h t ht => ((hb p hp s le_rfl (γ t) Ψ).2.1 h).trans (by
      rw [mul_assoc]
      have hR : rightTestSize (γ t) ≤ R := (show _ < R from ht).le
      have hR₀ := zero_le_one.trans (one_le_rightTestSize (γ t))
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR₀ hR _) (apply_nonneg _ _)) (hB₀ h)))
    (hBi.mul_const _) (ae_of_all _ fun h t _ => hDeriv t h)).2

variable (r) in
/-- Group continuity and the derivative through the translated Godement integral under uniform
smaller-rank estimates. The derivative on the test is taken before right translation. -/
def ComplexGodementParametricStatement : Prop :=
  ∀ {P : Type} (ν : Measure G) [ν.IsHaarMeasure] (μ : AdditiveHaarMeasure ℂ)
    (a : ℂˣ) (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ),
    (∀ p ∈ S, Continuous (W p)) → HasUniformSimpleRootBound S W →
    ∀ p ∈ S, ∀ (Φ : 𝓢(Rect, ℂ)) (s : ℂ),
      Continuous (fun g : G' => continuedValue ν μ d a Φ (W p) g s) ∧
      ∀ (γ : ℝ → G') (A : Rect →L[ℝ] Rect), Continuous γ →
        (∀ (t : ℝ) (Y : Rect), HasDerivAt (fun v => Y * (γ v).val) (A (Y * (γ t).val)) t) →
        ∀ t₀ : ℝ,
          HasDerivAt (fun t => ∫ h, iteratedKernel (complexScaledCharacter a) μ d
            (rightTest (γ t) Φ) (W p) s h ∂ν)
            (∫ h, iteratedKernel (complexScaledCharacter a) μ d
              (rightTest (γ t₀) (directionalTest A Φ)) (W p) s h ∂ν) t₀

theorem complexGodementParametric : ComplexGodementParametricStatement r := by
  intro P ν hν μ a d S W hWc hWb p hp Φ s
  exact ⟨continuous_continuedValue ν μ a d S W hWc hWb p hp Φ s,
    fun γ A hγ hD t₀ => hasDerivAt_integral_iteratedKernel_curve ν μ a d S W hWc hWb p hp Φ s γ hγ A hD t₀⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGodementParametric
