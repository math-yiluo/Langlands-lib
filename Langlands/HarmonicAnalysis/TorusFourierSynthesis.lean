import Langlands.HarmonicAnalysis.TorusFourierDecay

/-! # Fourier synthesis on a finite product of circles

For a measure `μ` on a space `X`, a measurable `n : X → (J → ℤ)` and `F : X → ℂ`, the Fourier
synthesis `z ↦ ∫ F(x) ∏ⱼ zⱼ^{n(x)ⱼ} dμ(x)` is a function on the torus `J → Circle`. If all the
moments `∫ ‖n(x)‖^k |F(x)| dμ(x)` are finite, it is smooth, its partial derivative in the `j`-th
angle is the synthesis of `x ↦ i n(x)ⱼ F(x)`, and its iterated partial derivatives along a list
`l` of directions are bounded by `∫ ‖n(x)‖^{|l|} |F(x)| dμ(x)`.

This is the mechanism of the proof of Waldspurger's Proposition VII.1.3, where
`χ ↦ ⟨(ω ⊗ χ)(f̌) v, v̌⟩ = ∫_G f̌(g) χ(g) ⟨ω(g) v, v̌⟩ dg` is shown to be smooth on `Im X(G)`.
-/

noncomputable section

open MeasureTheory Complex
open Langlands.Plancherel (IsSmoothFiniteTorusFunction finiteTorusExp
  isOpenQuotientMap_finiteTorusExp)
open scoped ContDiff

namespace Langlands.HarmonicAnalysis.TorusFourier

variable {J : Type*} [Fintype J]

/-- The real linear form `θ ↦ i ∑ⱼ mⱼ θⱼ` on angle space. -/
def angleForm (m : J → ℤ) : (J → ℝ) →L[ℝ] ℂ :=
  (∑ j, (m j : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) j).smulRight I

theorem angleForm_apply (m : J → ℤ) (θ : J → ℝ) :
    angleForm m θ = ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ) * I := by
  simp [angleForm, Complex.real_smul]

theorem norm_cexp_angleForm (m : J → ℤ) (θ : J → ℝ) : ‖cexp (angleForm m θ)‖ = 1 := by
  rw [angleForm_apply]
  exact norm_exp_ofReal_mul_I _

theorem torusCharacter_finiteTorusExp (m : J → ℤ) (θ : J → ℝ) :
    torusCharacter m (finiteTorusExp θ) = cexp (angleForm m θ) := by
  rw [angleForm_apply, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, torusCharacter]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [finiteTorusExp, ← Circle.exp_intCast_mul, Circle.coe_exp]

theorem norm_angleForm_le (m : J → ℤ) : ‖angleForm m‖ ≤ Fintype.card J * ‖m‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun θ => ?_
  rw [angleForm_apply, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc |∑ j, (m j : ℝ) * θ j| ≤ ∑ j, |(m j : ℝ) * θ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : J, ‖m‖ * ‖θ‖ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
        · have h := norm_le_pi_norm m j
          rwa [Int.norm_eq_abs] at h
        · exact (Real.norm_eq_abs (θ j)).symm.le.trans (norm_le_pi_norm θ j)
    _ = Fintype.card J * ‖m‖ * ‖θ‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- `c` times the form `θ ↦ i ∑ⱼ mⱼ θⱼ`, written coordinate by coordinate. -/
theorem smul_angleForm (c : ℂ) (m : J → ℤ) :
    c • angleForm m =
      ∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) j).smulRight
        (I * (m j : ℂ) * c) := by
  refine ContinuousLinearMap.ext fun θ => ?_
  simp only [FunLike.coe_smul, FunLike.coe_sum, Pi.smul_apply,
    Finset.sum_apply, angleForm_apply]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    Complex.real_smul, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_intCast, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

variable {X : Type*} [MeasurableSpace X]

/-- Fourier synthesis on the torus `J → Circle`: `z ↦ ∫ F(x) ∏ⱼ zⱼ^{n(x)ⱼ} dμ(x)`. -/
def torusSynthesis (μ : Measure X) (n : X → J → ℤ) (F : X → ℂ) (z : J → Circle) : ℂ :=
  ∫ x, F x * torusCharacter (n x) z ∂μ

/-- `F` is a.e. strongly measurable and has finite moments `∫ ‖n(x)‖^k |F(x)| dμ` of all
orders `k`. -/
def HasTorusMoments (μ : Measure X) (n : X → J → ℤ) (F : X → ℂ) : Prop :=
  AEStronglyMeasurable F μ ∧ ∀ k : ℕ, Integrable (fun x => ‖n x‖ ^ k * ‖F x‖) μ

variable {μ : Measure X} {n : X → J → ℤ} {F : X → ℂ}

theorem torusSynthesis_comp_finiteTorusExp (μ : Measure X) (n : X → J → ℤ) (F : X → ℂ) :
    torusSynthesis μ n F ∘ finiteTorusExp =
      fun θ => ∫ x, F x * cexp (angleForm (n x) θ) ∂μ := by
  funext θ
  simp only [Function.comp_apply, torusSynthesis, torusCharacter_finiteTorusExp]

theorem HasTorusMoments.integrable (hF : HasTorusMoments μ n F) : Integrable F μ :=
  (integrable_norm_iff hF.1).mp (by simpa using hF.2 0)

/-- Multiplying by a function of `n(x)` of polynomial growth preserves finite moments. -/
theorem HasTorusMoments.mul_left (hn : Measurable n) (hF : HasTorusMoments μ n F)
    (c : (J → ℤ) → ℂ) {p : ℕ} (hc : ∀ m, ‖c m‖ ≤ ‖m‖ ^ p) :
    HasTorusMoments μ n (fun x => c (n x) * F x) := by
  have hcm : Measurable fun x => c (n x) := (measurable_of_countable c).comp hn
  have hnm : Measurable fun x => ‖n x‖ := (measurable_of_countable fun m : J → ℤ => ‖m‖).comp hn
  refine ⟨hcm.aestronglyMeasurable.mul hF.1, fun k => ?_⟩
  refine (hF.2 (k + p)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((hnm.pow_const k).aestronglyMeasurable).mul
      (hcm.aestronglyMeasurable.mul hF.1).norm
  · rw [Real.norm_of_nonneg (by positivity), norm_mul, pow_add, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hc (n x)) (norm_nonneg _)) (by positivity)

theorem integrable_mul_cexp_angleForm (hn : Measurable n) (hF : HasTorusMoments μ n F)
    (θ : J → ℝ) : Integrable (fun x => F x * cexp (angleForm (n x) θ)) μ := by
  refine hF.integrable.norm.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact hF.1.mul ((measurable_of_countable fun m : J → ℤ =>
      cexp (angleForm m θ)).comp hn).aestronglyMeasurable
  · rw [norm_mul, norm_cexp_angleForm, mul_one]

theorem HasTorusMoments.integrable_mul_torusCharacter (hn : Measurable n)
    (hF : HasTorusMoments μ n F) (z : J → Circle) :
    Integrable (fun x => F x * torusCharacter (n x) z) μ := by
  refine hF.integrable.norm.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact hF.1.mul ((measurable_of_countable fun m : J → ℤ =>
      torusCharacter m z).comp hn).aestronglyMeasurable
  · rw [norm_mul, norm_torusCharacter, mul_one]

theorem HasTorusMoments.add (hn : Measurable n) {F₁ F₂ : X → ℂ} (h₁ : HasTorusMoments μ n F₁)
    (h₂ : HasTorusMoments μ n F₂) : HasTorusMoments μ n (fun x => F₁ x + F₂ x) := by
  have hnm : Measurable fun x => ‖n x‖ := (measurable_of_countable fun m : J → ℤ => ‖m‖).comp hn
  refine ⟨h₁.1.add h₂.1, fun k => ((h₁.2 k).add (h₂.2 k)).mono' ?_
    (Filter.Eventually.of_forall fun x => ?_)⟩
  · exact (hnm.pow_const k).aestronglyMeasurable.mul (h₁.1.add h₂.1).norm
  · rw [Real.norm_of_nonneg (by positivity), Pi.add_apply, ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)

/-- The synthesis is additive in `F` on functions with finite moments. -/
theorem torusSynthesis_add (hn : Measurable n) {F₁ F₂ : X → ℂ} (h₁ : HasTorusMoments μ n F₁)
    (h₂ : HasTorusMoments μ n F₂) :
    torusSynthesis μ n (fun x => F₁ x + F₂ x) = torusSynthesis μ n F₁ + torusSynthesis μ n F₂ := by
  funext z
  simp only [torusSynthesis, Pi.add_apply, add_mul]
  exact integral_add (h₁.integrable_mul_torusCharacter hn z)
    (h₂.integrable_mul_torusCharacter hn z)

/-- The synthesis commutes with multiplication by a constant. -/
theorem torusSynthesis_const_mul (μ : Measure X) (n : X → J → ℤ) (c : ℂ) (F : X → ℂ) :
    torusSynthesis μ n (fun x => c * F x) = c • torusSynthesis μ n F := by
  funext z
  simp only [torusSynthesis, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

/-- The derivative of the angle lift of a Fourier synthesis: its differential at `θ₀` is
`v ↦ ∑ⱼ vⱼ Φⱼ(θ₀)`, where `Φⱼ` is the synthesis of `x ↦ i n(x)ⱼ F(x)`. -/
theorem hasFDerivAt_torusSynthesis_comp (hn : Measurable n) (hF : HasTorusMoments μ n F)
    (θ₀ : J → ℝ) :
    HasFDerivAt (torusSynthesis μ n F ∘ finiteTorusExp)
      (∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) j).smulRight
        (torusSynthesis μ n (fun x => I * (n x j : ℂ) * F x) (finiteTorusExp θ₀))) θ₀ := by
  have hG : ∀ j, HasTorusMoments μ n (fun x => I * (n x j : ℂ) * F x) := fun j =>
    hF.mul_left hn (fun m => I * (m j : ℂ)) (p := 1) fun m => by
      rw [norm_mul, Complex.norm_I, one_mul, pow_one, Complex.norm_intCast, ← Int.norm_eq_abs]
      exact norm_le_pi_norm m j
  rw [torusSynthesis_comp_finiteTorusExp]
  have hderiv : ∀ x θ, HasFDerivAt (fun θ => F x * cexp (angleForm (n x) θ))
      (∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) j).smulRight
        (I * (n x j : ℂ) * F x * cexp (angleForm (n x) θ))) θ := fun x θ => by
    refine ((angleForm (n x)).hasFDerivAt.cexp.const_mul (F x)).congr_fderiv ?_
    rw [smul_smul, smul_angleForm]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (x₀ := θ₀)
    (F := fun θ x => F x * cexp (angleForm (n x) θ))
    (F' := fun θ x => ∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) j).smulRight
        (I * (n x j : ℂ) * F x * cexp (angleForm (n x) θ)))
    (bound := fun x => Fintype.card J * (‖n x‖ ^ 1 * ‖F x‖)) Filter.univ_mem
    (Filter.Eventually.of_forall fun θ => (integrable_mul_cexp_angleForm hn hF θ).1)
    (integrable_mul_cexp_angleForm hn hF θ₀)
    (Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      ((ContinuousLinearMap.smulRightL ℝ (J → ℝ) ℂ
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) j)).continuous.comp_aestronglyMeasurable
          (integrable_mul_cexp_angleForm hn (hG j) θ₀).1))
    (Filter.Eventually.of_forall fun x θ _ => by
      rw [(hderiv x θ).unique ((angleForm (n x)).hasFDerivAt.cexp.const_mul (F x)), norm_smul,
        norm_smul, norm_cexp_angleForm, one_mul, pow_one]
      calc ‖F x‖ * ‖angleForm (n x)‖ ≤ ‖F x‖ * (Fintype.card J * ‖n x‖) :=
            mul_le_mul_of_nonneg_left (norm_angleForm_le _) (norm_nonneg _)
        _ = Fintype.card J * (‖n x‖ * ‖F x‖) := by ring)
    ((hF.2 1).const_mul _)
    (Filter.Eventually.of_forall fun x θ _ => hderiv x θ)
  have hint : ∀ j ∈ Finset.univ, Integrable (fun x =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) j).smulRight
        (I * (n x j : ℂ) * F x * cexp (angleForm (n x) θ₀))) μ := fun j _ =>
    (ContinuousLinearMap.smulRightL ℝ (J → ℝ) ℂ
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) j)).integrable_comp
        (integrable_mul_cexp_angleForm hn (hG j) θ₀)
  convert key using 1
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := (ContinuousLinearMap.smulRightL ℝ (J → ℝ) ℂ
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) j)).integral_comp_comm
      (integrable_mul_cexp_angleForm hn (hG j) θ₀)
  simp only [ContinuousLinearMap.smulRightL_apply_apply] at h
  rw [h]
  congr 1
  exact congrFun (torusSynthesis_comp_finiteTorusExp μ n _) θ₀

theorem contDiff_torusSynthesis_comp (hn : Measurable n) :
    ∀ (k : ℕ) {F : X → ℂ}, HasTorusMoments μ n F →
      ContDiff ℝ k (torusSynthesis μ n F ∘ finiteTorusExp)
  | 0, F, hF => contDiff_zero.mpr
      (continuous_iff_continuousAt.mpr fun θ =>
        (hasFDerivAt_torusSynthesis_comp hn hF θ).continuousAt)
  | k + 1, F, hF => by
      have hG : ∀ j, HasTorusMoments μ n (fun x => I * (n x j : ℂ) * F x) := fun j =>
        hF.mul_left hn (fun m => I * (m j : ℂ)) (p := 1) fun m => by
          rw [norm_mul, Complex.norm_I, one_mul, pow_one, Complex.norm_intCast,
            ← Int.norm_eq_abs]
          exact norm_le_pi_norm m j
      rw [Nat.cast_add_one, contDiff_succ_iff_hasFDerivAt]
      refine ⟨_, ?_, hasFDerivAt_torusSynthesis_comp hn hF⟩
      exact ContDiff.sum fun j _ =>
        contDiff_const.smulRight (contDiff_torusSynthesis_comp hn k (hG j))

/-- A Fourier synthesis with finite moments of all orders is smooth on the torus. -/
theorem isSmoothFiniteTorusFunction_torusSynthesis (hn : Measurable n)
    (hF : HasTorusMoments μ n F) : IsSmoothFiniteTorusFunction (torusSynthesis μ n F) :=
  contDiff_infty.mpr fun k => contDiff_torusSynthesis_comp hn k hF

variable [DecidableEq J]

/-- The partial derivative in the `j`-th angle of a Fourier synthesis is the synthesis of
`x ↦ i n(x)ⱼ F(x)`. -/
theorem torusPartialDeriv_torusSynthesis (hn : Measurable n) (hF : HasTorusMoments μ n F)
    (j : J) :
    torusPartialDeriv j (torusSynthesis μ n F) =
      torusSynthesis μ n (fun x => I * (n x j : ℂ) * F x) := by
  funext z
  obtain ⟨θ, rfl⟩ := (isOpenQuotientMap_finiteTorusExp J).surjective z
  rw [torusPartialDeriv_finiteTorusExp (isSmoothFiniteTorusFunction_torusSynthesis hn hF),
    (hasFDerivAt_torusSynthesis_comp hn hF θ).fderiv]
  simp [Pi.single_apply]

/-- The composite `∂_{j₁} ∘ ⋯ ∘ ∂_{jₖ}` of partial derivatives along the list `[j₁, …, jₖ]`. -/
def torusPartialDerivList (l : List J) (f : (J → Circle) → ℂ) : (J → Circle) → ℂ :=
  l.foldr torusPartialDeriv f

omit [DecidableEq J] in
theorem norm_list_prod_I_mul_le (l : List J) (m : J → ℤ) :
    ‖(l.map fun j => I * (m j : ℂ)).prod‖ ≤ ‖m‖ ^ l.length := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, norm_mul, norm_mul, Complex.norm_I, one_mul,
      List.length_cons, pow_succ']
    refine mul_le_mul ?_ ih (norm_nonneg _) (norm_nonneg _)
    rw [Complex.norm_intCast, ← Int.norm_eq_abs]
    exact norm_le_pi_norm m j

/-- Iterated partial derivatives of a Fourier synthesis along a list `l`: the synthesis of
`x ↦ (∏_{j ∈ l} i n(x)ⱼ) F(x)`. -/
theorem torusPartialDerivList_torusSynthesis (hn : Measurable n) (hF : HasTorusMoments μ n F)
    (l : List J) :
    torusPartialDerivList l (torusSynthesis μ n F) =
      torusSynthesis μ n (fun x => (l.map fun j => I * (n x j : ℂ)).prod * F x) := by
  induction l with
  | nil => simp [torusPartialDerivList]
  | cons j l ih =>
    have hl : HasTorusMoments μ n (fun x => (l.map fun j => I * (n x j : ℂ)).prod * F x) :=
      hF.mul_left hn (fun m => (l.map fun j => I * (m j : ℂ)).prod) (norm_list_prod_I_mul_le l)
    change torusPartialDeriv j (torusPartialDerivList l (torusSynthesis μ n F)) = _
    rw [ih, torusPartialDeriv_torusSynthesis hn hl]
    congr 1
    funext x
    simp only [List.map_cons, List.prod_cons]
    ring

omit [DecidableEq J] in
theorem norm_torusSynthesis_le (μ : Measure X) (n : X → J → ℤ) (F : X → ℂ) (z : J → Circle) :
    ‖torusSynthesis μ n F z‖ ≤ ∫ x, ‖F x‖ ∂μ := by
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_mul, norm_torusCharacter, mul_one]

/-- The bound on iterated partial derivatives of a Fourier synthesis:
`|∂_l Φ(z)| ≤ ∫ ‖n(x)‖^{|l|} |F(x)| dμ`. -/
theorem norm_torusPartialDerivList_torusSynthesis_le (hn : Measurable n)
    (hF : HasTorusMoments μ n F) (l : List J) (z : J → Circle) :
    ‖torusPartialDerivList l (torusSynthesis μ n F) z‖ ≤
      ∫ x, ‖n x‖ ^ l.length * ‖F x‖ ∂μ := by
  have hl : HasTorusMoments μ n (fun x => (l.map fun j => I * (n x j : ℂ)).prod * F x) :=
    hF.mul_left hn (fun m => (l.map fun j => I * (m j : ℂ)).prod) (norm_list_prod_I_mul_le l)
  rw [torusPartialDerivList_torusSynthesis hn hF]
  refine (norm_torusSynthesis_le μ n _ z).trans (integral_mono hl.integrable.norm
    (hF.2 l.length) fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_list_prod_I_mul_le l (n x)) (norm_nonneg _)

end Langlands.HarmonicAnalysis.TorusFourier
