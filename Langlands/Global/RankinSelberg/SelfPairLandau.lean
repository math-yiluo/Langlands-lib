import Langlands.Analysis.LandauMellin
import Langlands.Global.RankinSelberg.PartialEqualWhittakerIntegral
import Langlands.Global.RankinSelberg.PartialIntegralExhaustion
import Langlands.Global.RankinSelberg.UnequalGaugeReduction

/-! # Landau's theorem for Whittaker–Mellin integrals with nonnegative weight

Let `G s q = f q * exp (s * log |det q.out|)` on `N_n(𝔸) \ GL_n(𝔸)` with `f ≥ 0`. This is the
shape of the self-pair integrand `|W(g)|² Φ(e_n g) |det g|^s`. Suppose `G s` is integrable on
`σ₁ < Re s` and its integral agrees there with a function holomorphic on `σ₀ < Re s`.
Then `G s` is integrable on `σ₀ < Re s`, and `s ↦ ∫_A G s` is holomorphic there for every
set `A`. At real points these integrals are nonnegative reals, monotone in `A`, and their
positivity does not depend on the real point. See the paired Markdown.
-/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.SelfPairLandau

local instance selfPairLandauSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance selfPairLandauSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F]

/-- The Mellin phase `log |det g|` at the representative `g` of a class of
`N_n(𝔸) \ GL_n(𝔸)`. -/
def logDet (n : ℕ) (q : WhittakerQuotient F n) : ℝ :=
  Real.log (detNorm F n q.out)

/-- `|det g|` read at the representative is the descent of the left `N_n(𝔸)`-invariant
function `|det|`. -/
theorem detNorm_out_eq_lift (n : ℕ) (q : WhittakerQuotient F n) :
    detNorm F n q.out = LeftCosetSpace.lift (unipotentAdelic F n) (detNorm F n)
      (fun a x => GaugeReduction.detNorm_unipotent_mul F n a x) q := by
  conv_rhs => rw [← Quotient.out_eq q]
  rfl

theorem continuous_detNorm_out (n : ℕ) :
    Continuous fun q : WhittakerQuotient F n => detNorm F n q.out := by
  rw [show (fun q : WhittakerQuotient F n => detNorm F n q.out) =
      LeftCosetSpace.lift (unipotentAdelic F n) (detNorm F n)
        (fun a x => GaugeReduction.detNorm_unipotent_mul F n a x) from funext (detNorm_out_eq_lift n)]
  exact LeftCosetSpace.continuous_lift _ _ _ (UnequalAnalytic.continuous_detNorm F n)

theorem measurable_logDet (n : ℕ) : Measurable (logDet (F := F) n) :=
  Real.measurable_log.comp (continuous_detNorm_out n).measurable

section Mellin

variable {r : ℕ} {G : ℂ → WhittakerQuotient F (r + 1) → ℂ}
  {f : WhittakerQuotient F (r + 1) → ℝ}

/-- The Mellin form of the integrand. -/
def IsMellin (G : ℂ → WhittakerQuotient F (r + 1) → ℂ) (f : WhittakerQuotient F (r + 1) → ℝ) :
    Prop :=
  ∀ (s : ℂ) (q : WhittakerQuotient F (r + 1)),
    G s q = (f q : ℂ) * Complex.exp (s * (Real.log (detNorm F (r + 1) q.out) : ℂ))

theorem IsMellin.apply_real (hG : IsMellin G f) (σ : ℝ) (q : WhittakerQuotient F (r + 1)) :
    G σ q = ((f q * Real.exp (σ * logDet (r + 1) q) : ℝ) : ℂ) := by
  rw [hG, logDet]
  push_cast
  rfl

theorem IsMellin.norm_apply_real (hG : IsMellin G f) (hf : ∀ q, 0 ≤ f q) (σ : ℝ)
    (q : WhittakerQuotient F (r + 1)) :
    ‖G σ q‖ = f q * Real.exp (σ * logDet (r + 1) q) := by
  rw [hG.apply_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (hf q) (Real.exp_pos _).le)]

/-- The integrand is the two-sided transform integrand of `LandauMellin.bilateral`. -/
theorem IsMellin.eq_bilateral (hG : IsMellin G f) (s : ℂ) :
    G s = fun q => (f q : ℂ) * Complex.exp (s * (logDet (r + 1) q : ℂ)) :=
  funext fun q => hG s q

variable {ν : Measure (WhittakerQuotient F (r + 1))}

/-- The weight is almost everywhere strongly measurable once the integrand is, at one real
point. -/
theorem IsMellin.aestronglyMeasurable_weight (hG : IsMellin G f) {σ : ℝ}
    (h : AEStronglyMeasurable (G σ) ν) : AEStronglyMeasurable f ν := by
  have hre : AEStronglyMeasurable (fun q => (G σ q).re) ν :=
    Complex.continuous_re.comp_aestronglyMeasurable h
  have hexp : AEStronglyMeasurable (fun q => Real.exp (-(σ * logDet (r + 1) q))) ν :=
    (Real.measurable_exp.comp ((measurable_const.mul (measurable_logDet (r + 1))).neg))
      |>.aestronglyMeasurable
  refine (hre.mul hexp).congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Pi.mul_apply, hG.apply_real, Complex.ofReal_re]
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- Integrability of the real Mellin integrand from that of `G` at a real point. -/
theorem IsMellin.integrable_real (hG : IsMellin G f) (hf : ∀ q, 0 ≤ f q) {σ : ℝ}
    (h : Integrable (G σ) ν) :
    Integrable (fun q => f q * Real.exp (σ * logDet (r + 1) q)) ν :=
  h.norm.congr (Filter.Eventually.of_forall fun q => hG.norm_apply_real hf σ q)

/-- Integrability of `G s` from that of the real Mellin integrand at `Re s`. -/
theorem IsMellin.integrable_of_real (hG : IsMellin G f) (hf : ∀ q, 0 ≤ f q)
    (hfm : AEStronglyMeasurable f ν) {s : ℂ}
    (h : Integrable (fun q => f q * Real.exp (s.re * logDet (r + 1) q)) ν) :
    Integrable (G s) ν := by
  rw [hG.eq_bilateral]
  exact LandauMellin.integrable_bilateral hfm (measurable_logDet (r + 1)).aestronglyMeasurable
    (Filter.Eventually.of_forall hf) h

/-- **Landau's theorem for the Whittaker–Mellin integral.** If `G s` is integrable for
`σ₁ < Re s`, and its integral agrees there with a function holomorphic on `σ₀ < Re s`, then
`G s` is integrable for every `s` with `σ₀ < Re s`. -/
theorem IsMellin.integrable_of_differentiableOn (hG : IsMellin G f) (hf : ∀ q, 0 ≤ f q)
    {σ₀ σ₁ : ℝ} (hint : ∀ s : ℂ, σ₁ < s.re → Integrable (G s) ν) {I : ℂ → ℂ}
    (hI : DifferentiableOn ℂ I {s : ℂ | σ₀ < s.re})
    (hIG : ∀ s : ℂ, σ₁ < s.re → I s = ∫ q, G s q ∂ν) :
    ∀ s : ℂ, σ₀ < s.re → Integrable (G s) ν := by
  have hfm : AEStronglyMeasurable f ν :=
    hG.aestronglyMeasurable_weight (σ := σ₁ + 1)
      (hint _ (by rw [Complex.ofReal_re]; linarith)).aestronglyMeasurable
  have h₁ : ∀ σ : ℝ, σ₁ < σ →
      Integrable (fun q => f q * Real.exp (σ * logDet (r + 1) q)) ν := fun σ hσ =>
    hG.integrable_real hf (hint σ (by rw [Complex.ofReal_re]; exact hσ))
  have hL := LandauMellin.integrable_of_differentiableOn hfm
    (measurable_logDet (r + 1)).aestronglyMeasurable (Filter.Eventually.of_forall hf) h₁ hI
    (fun s hs => by rw [hIG s hs, hG.eq_bilateral]; rfl)
  intro s hs
  exact hG.integrable_of_real hf hfm (hL s.re hs)

/-- Under the hypotheses of Landau's theorem, the real Mellin integrand is integrable at every
real point `σ > σ₀`. -/
theorem IsMellin.integrable_real_of_differentiableOn (hG : IsMellin G f) (hf : ∀ q, 0 ≤ f q)
    {σ₀ σ₁ : ℝ} (hint : ∀ s : ℂ, σ₁ < s.re → Integrable (G s) ν) {I : ℂ → ℂ}
    (hI : DifferentiableOn ℂ I {s : ℂ | σ₀ < s.re})
    (hIG : ∀ s : ℂ, σ₁ < s.re → I s = ∫ q, G s q ∂ν) {σ : ℝ} (hσ : σ₀ < σ) :
    Integrable (fun q => f q * Real.exp (σ * logDet (r + 1) q)) ν :=
  hG.integrable_real hf
    (hG.integrable_of_differentiableOn hf hint hI hIG σ (by rw [Complex.ofReal_re]; exact hσ))

/-- Holomorphy of every partial integral: if `G s` is integrable for every `s` with
`σ₀ < Re s`, then `s ↦ ∫_A G s` is holomorphic on `σ₀ < Re s` for every set `A`. -/
theorem IsMellin.differentiableOn_setIntegral (hG : IsMellin G f) (hf : ∀ q, 0 ≤ f q)
    {σ₀ : ℝ} (hint : ∀ s : ℂ, σ₀ < s.re → Integrable (G s) ν)
    (A : Set (WhittakerQuotient F (r + 1))) :
    DifferentiableOn ℂ (fun s => ∫ q in A, G s q ∂ν) {s : ℂ | σ₀ < s.re} := by
  have hfm : AEStronglyMeasurable f ν :=
    hG.aestronglyMeasurable_weight (σ := σ₀ + 1)
      (hint _ (by rw [Complex.ofReal_re]; linarith)).aestronglyMeasurable
  have h : ∀ σ : ℝ, σ₀ < σ →
      Integrable (fun q => f q * Real.exp (σ * logDet (r + 1) q)) (ν.restrict A) :=
    fun σ hσ => (hG.integrable_real hf (hint σ (by rw [Complex.ofReal_re]; exact hσ))).restrict
  have hD := LandauMellin.differentiableOn_bilateral hfm.restrict
    (measurable_logDet (r + 1)).aestronglyMeasurable.restrict
    (ae_restrict_of_ae (Filter.Eventually.of_forall hf)) h
  refine hD.congr fun s _ => ?_
  show ∫ q in A, G s q ∂ν = ∫ q, (f q : ℂ) * Complex.exp (s * (logDet (r + 1) q : ℂ)) ∂ν.restrict A
  rw [hG.eq_bilateral]

/-- The full integral is holomorphic on `σ₀ < Re s` when `G s` is integrable there. -/
theorem IsMellin.differentiableOn_integral (hG : IsMellin G f) (hf : ∀ q, 0 ≤ f q)
    {σ₀ : ℝ} (hint : ∀ s : ℂ, σ₀ < s.re → Integrable (G s) ν) :
    DifferentiableOn ℂ (fun s => ∫ q, G s q ∂ν) {s : ℂ | σ₀ < s.re} := by
  have h := hG.differentiableOn_setIntegral hf hint Set.univ
  simp only [Measure.restrict_univ] at h
  exact h

/-! ### Values at real points -/

/-- At a real point, a partial integral is the real integral of the nonnegative Mellin
integrand. -/
theorem IsMellin.setIntegral_real (hG : IsMellin G f) (A : Set (WhittakerQuotient F (r + 1)))
    (σ : ℝ) :
    ∫ q in A, G σ q ∂ν = ((∫ q in A, f q * Real.exp (σ * logDet (r + 1) q) ∂ν : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  exact integral_congr_ae (Filter.Eventually.of_forall fun q => hG.apply_real σ q)

theorem setIntegral_real_nonneg (hf : ∀ q, 0 ≤ f q)
    (A : Set (WhittakerQuotient F (r + 1))) (σ : ℝ) :
    0 ≤ ∫ q in A, f q * Real.exp (σ * logDet (r + 1) q) ∂ν :=
  integral_nonneg fun q => mul_nonneg (hf q) (Real.exp_pos _).le

/-- Monotonicity in the set of integration. -/
theorem setIntegral_real_mono (hf : ∀ q, 0 ≤ f q)
    {A B : Set (WhittakerQuotient F (r + 1))} (hAB : A ⊆ B) {σ : ℝ}
    (h : Integrable (fun q => f q * Real.exp (σ * logDet (r + 1) q)) ν) :
    ∫ q in A, f q * Real.exp (σ * logDet (r + 1) q) ∂ν ≤
      ∫ q in B, f q * Real.exp (σ * logDet (r + 1) q) ∂ν :=
  setIntegral_mono_set h.integrableOn
    (Filter.Eventually.of_forall fun q => mul_nonneg (hf q) (Real.exp_pos _).le)
    (Filter.Eventually.of_forall hAB)

theorem support_mul_exp (f : WhittakerQuotient F (r + 1) → ℝ) (σ : ℝ) :
    Function.support (fun q => f q * Real.exp (σ * logDet (r + 1) q)) = Function.support f := by
  ext q
  simp [Real.exp_ne_zero]

/-- Positivity of a partial integral at a real point is equivalent to positivity of the
measure of the support of the weight inside the set of integration. -/
theorem setIntegral_real_pos_iff (hf : ∀ q, 0 ≤ f q)
    (A : Set (WhittakerQuotient F (r + 1))) {σ : ℝ}
    (h : Integrable (fun q => f q * Real.exp (σ * logDet (r + 1) q)) ν) :
    0 < ∫ q in A, f q * Real.exp (σ * logDet (r + 1) q) ∂ν ↔
      0 < ν.restrict A (Function.support f) := by
  rw [integral_pos_iff_support_of_nonneg
    (fun q => mul_nonneg (hf q) (Real.exp_pos _).le) h.restrict, support_mul_exp]

/-- Positivity of a partial integral does not depend on the real point. -/
theorem setIntegral_real_pos_iff_pos (hf : ∀ q, 0 ≤ f q)
    (A : Set (WhittakerQuotient F (r + 1))) {σ σ' : ℝ}
    (h : Integrable (fun q => f q * Real.exp (σ * logDet (r + 1) q)) ν)
    (h' : Integrable (fun q => f q * Real.exp (σ' * logDet (r + 1) q)) ν) :
    0 < ∫ q in A, f q * Real.exp (σ * logDet (r + 1) q) ∂ν ↔
      0 < ∫ q in A, f q * Real.exp (σ' * logDet (r + 1) q) ∂ν := by
  rw [setIntegral_real_pos_iff hf A h, setIntegral_real_pos_iff hf A h']

end Mellin

/-! ### The partial equal-rank Whittaker integrals -/

section Partial

variable {r : ℕ} {W W' : Points F (r + 1) → ℂ} {Φ : RowVector F (r + 1) → ℂ}
  {f : WhittakerQuotient F (r + 1) → ℝ}

/-- **Landau for the equal-rank Whittaker integral.** If `W(g) W'(g) Φ(e_n g)` is a
nonnegative weight, the integrand is integrable on `σ₁ < Re s`, and the integral agrees there
with a function holomorphic on `σ₀ < Re s`, then the integrand is integrable on `σ₀ < Re s`
and every partial integral `Ψ_(S∪∞)` is holomorphic there. -/
theorem integrable_and_differentiableOn_partial
    (hG : IsMellin (equalWhittakerIntegrand F W W' Φ) f) (hf : ∀ q, 0 ≤ f q)
    {σ₀ σ₁ : ℝ}
    (hint : ∀ s : ℂ, σ₁ < s.re →
      Integrable (equalWhittakerIntegrand F W W' Φ s) (whittakerQuotientMeasure F (r + 1)))
    {I : ℂ → ℂ} (hI : DifferentiableOn ℂ I {s : ℂ | σ₀ < s.re})
    (hIG : ∀ s : ℂ, σ₁ < s.re → I s = equalWhittakerIntegral F W W' Φ s) :
    (∀ s : ℂ, σ₀ < s.re →
      Integrable (equalWhittakerIntegrand F W W' Φ s) (whittakerQuotientMeasure F (r + 1))) ∧
    DifferentiableOn ℂ (equalWhittakerIntegral F W W' Φ) {s : ℂ | σ₀ < s.re} ∧
    ∀ S : Finset (FinitePlace F),
      DifferentiableOn ℂ (partialEqualWhittakerIntegral F S W W' Φ) {s : ℂ | σ₀ < s.re} := by
  have hint₀ := hG.integrable_of_differentiableOn hf hint hI hIG
  exact ⟨hint₀, hG.differentiableOn_integral hf hint₀,
    fun S => hG.differentiableOn_setIntegral hf hint₀ _⟩

/-- At a real point, the partial integral `Ψ_(S∪∞)` is the real integral of the nonnegative
Mellin integrand over the classes integral outside `S`. -/
theorem partialEqualWhittakerIntegral_real
    (hG : IsMellin (equalWhittakerIntegrand F W W' Φ) f) (S : Finset (FinitePlace F)) (σ : ℝ) :
    partialEqualWhittakerIntegral F S W W' Φ σ =
      ((∫ q in unipotentIntegralClasses F (r + 1) S,
        f q * Real.exp (σ * logDet (r + 1) q) ∂whittakerQuotientMeasure F (r + 1) : ℝ) : ℂ) :=
  hG.setIntegral_real _ σ

/-- If the partial integral `Ψ_(S∪∞)` has positive real part at one real point where the
integrand is integrable, its real Mellin integral is positive at every real point where the
integrand is integrable. -/
theorem setIntegral_real_pos_of_re_pos
    (hG : IsMellin (equalWhittakerIntegrand F W W' Φ) f) (hf : ∀ q, 0 ≤ f q)
    {S : Finset (FinitePlace F)} {σ₀ σ : ℝ}
    (h₀ : Integrable (equalWhittakerIntegrand F W W' Φ σ₀) (whittakerQuotientMeasure F (r + 1)))
    (h : Integrable (equalWhittakerIntegrand F W W' Φ σ) (whittakerQuotientMeasure F (r + 1)))
    (hpos : 0 < (partialEqualWhittakerIntegral F S W W' Φ σ₀).re) :
    0 < ∫ q in unipotentIntegralClasses F (r + 1) S,
      f q * Real.exp (σ * logDet (r + 1) q) ∂whittakerQuotientMeasure F (r + 1) := by
  rw [partialEqualWhittakerIntegral_real hG, Complex.ofReal_re] at hpos
  exact (setIntegral_real_pos_iff_pos hf _ (hG.integrable_real hf h₀)
    (hG.integrable_real hf h)).1 hpos

end Partial

end Langlands.Global.RankinSelbergGlobal.SelfPairLandau
