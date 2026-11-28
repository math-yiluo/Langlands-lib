import Langlands.BaseChange.SupercuspidalCutoffTraces

/-!
# Pseudo-coefficients of supercuspidal representations with vanishing constant terms

For a nonarchimedean local field `F`, `0 < n`, an irreducible supercuspidal representation `π`
of `GL_n(F)` with central character `χ` and a Haar measure `μ`, there is a Schwartz–Bruhat
function `f` with vanishing constant terms, `tr π(f) = 1` and `tr ρ(f) = 0` for every
irreducible admissible `ρ ≇ π` with central character `χ`
(`exists_cuspForm_pseudoCoefficient`).

The nonvanishing of the Schur constant uses the positive semi-definite Hermitian form
`B(x, y) = ∫_{0 ≤ ord det < n} ℓ₀(π(g⁻¹) x) \overline{ℓ₀(π(g⁻¹) y)} r^{ord det g} dμ(g)`,
where `r ^ n = ‖χ(ϖ)‖²`, which satisfies `B(π(h) x, π(h) y) = r^{ord det h} B(x, y)`.
-/

noncomputable section

namespace Langlands.BaseChange.SupercuspidalCutoff

open MeasureTheory HarmonicAnalysis PeriodicWindow
open scoped ComplexConjugate

universe u uV uW

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

section Weight

variable (χ : Subgroup.center (GeneralLinear n F) →* ℂˣ)

/-- The positive real number `r` with `r ^ n = ‖χ(ϖ)‖²`. -/
def weightBase : ℝ := (‖(χ centralUniformizerCenter : ℂ)‖ ^ 2) ^ ((n : ℝ)⁻¹)

/-- The weight `g ↦ r ^ (ord det g)`. -/
def weight (g : GeneralLinear n F) : ℝ := weightBase χ ^ detOrd g

theorem weightBase_pos : 0 < weightBase χ :=
  Real.rpow_pos_of_pos (pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) 2) _

theorem weight_pos (g : GeneralLinear n F) : 0 < weight χ g := zpow_pos (weightBase_pos χ) _

theorem weight_mul (g h : GeneralLinear n F) : weight χ (g * h) = weight χ g * weight χ h := by
  rw [weight, weight, weight, detOrd_mul, zpow_add₀ (weightBase_pos χ).ne']

theorem weight_of_detOrd_eq_zero {g : GeneralLinear n F} (hg : detOrd g = 0) :
    weight χ g = 1 := by
  rw [weight, hg, zpow_zero]

theorem weight_centralUniformizer_mul (hn : 0 < n) (g : GeneralLinear n F) :
    weight χ (centralUniformizer * g) =
      ‖(χ centralUniformizerCenter : ℂ)‖ ^ 2 * weight χ g := by
  rw [weight_mul]
  congr 1
  rw [weight, detOrd_centralUniformizer, zpow_natCast, weightBase,
    Real.rpow_inv_natCast_pow (by positivity) hn.ne']

theorem isLocallyConstant_weight : IsLocallyConstant (weight χ : GeneralLinear n F → ℝ) :=
  isLocallyConstant_detOrd.comp (fun d : ℤ => weightBase χ ^ d)

end Weight

section Form

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear n F) V) (ℓ₀ : Module.Dual ℂ V)
  (χ : Subgroup.center (GeneralLinear n F) →* ℂˣ)

/-- The integrand `ℓ₀(π(g⁻¹) x) \overline{ℓ₀(π(g⁻¹) y)} r^{ord det g}` of the form. -/
def formIntegrand (x y : V) (g : GeneralLinear n F) : ℂ :=
  coeff π ℓ₀ x g * conj (coeff π ℓ₀ y g) * (weight χ g : ℂ)

theorem formIntegrand_central (hn : 0 < n) (hπχ : HasCentralCharacterRep π χ) (x y : V)
    (g : GeneralLinear n F) :
    formIntegrand π ℓ₀ χ x y (centralUniformizer * g) = formIntegrand π ℓ₀ χ x y g := by
  let zc : Subgroup.center (GeneralLinear n F) := centralUniformizerCenter
  have hx : coeff π ℓ₀ x (centralUniformizer * g) = (χ zc⁻¹ : ℂ) * coeff π ℓ₀ x g :=
    coeff_central_mul π ℓ₀ hπχ zc x g
  have hy : coeff π ℓ₀ y (centralUniformizer * g) = (χ zc⁻¹ : ℂ) * coeff π ℓ₀ y g :=
    coeff_central_mul π ℓ₀ hπχ zc y g
  have key : (χ zc⁻¹ : ℂ) * conj (χ zc⁻¹ : ℂ) * ((‖(χ zc : ℂ)‖ : ℂ) ^ 2) = 1 := by
    rw [Complex.mul_conj', ← mul_pow, ← Complex.ofReal_mul, ← norm_mul,
      character_inv_mul_character, norm_one, Complex.ofReal_one, one_pow]
  simp only [formIntegrand]
  rw [hx, hy, weight_centralUniformizer_mul χ hn, map_mul]
  push_cast
  linear_combination (coeff π ℓ₀ x g * conj (coeff π ℓ₀ y g) * (weight χ g : ℂ)) * key

theorem formIntegrand_rho (x y : V) (h g : GeneralLinear n F) :
    formIntegrand π ℓ₀ χ (π h x) (π h y) g =
      (weight χ h : ℂ) * formIntegrand π ℓ₀ χ x y (h⁻¹ * g) := by
  simp only [formIntegrand, coeff_rho]
  have hw : weight χ g = weight χ h * weight χ (h⁻¹ * g) := by
    rw [← weight_mul, mul_inv_cancel_left]
  rw [hw]
  push_cast
  ring

theorem continuous_conj_coeff_mul_weight [IsTopologicalGroup (GeneralLinear n F)]
    (hπ : IsSmooth π) (y : V) :
    Continuous fun g => conj (coeff π ℓ₀ y g) * (weight χ g : ℂ) :=
  (Complex.continuous_conj.comp ((isLocallyConstant_coeff π ℓ₀ hπ y).continuous)).mul
    (Complex.continuous_ofReal.comp (isLocallyConstant_weight χ).continuous)

theorem window_formIntegrand_eq (x y : V) (g : GeneralLinear n F) :
    (window detOrd n 0).indicator (formIntegrand π ℓ₀ χ x y) g =
      cutoffFun π ℓ₀ x g * (conj (coeff π ℓ₀ y g) * (weight χ g : ℂ)) := by
  by_cases hg : g ∈ window detOrd n 0
  · rw [cutoffFun, Set.indicator_of_mem hg, Set.indicator_of_mem hg, formIntegrand, mul_assoc]
  · rw [cutoffFun, Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]

variable [T2Space (GeneralLinear n F)] [MeasurableSpace (GeneralLinear n F)]
  [BorelSpace (GeneralLinear n F)] (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure]

theorem integrable_levelSet_formIntegrand (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ₀ : IsSmoothVector π.dual ℓ₀) (x y : V) (j : ℤ) :
    Integrable ((levelSet detOrd j).indicator (formIntegrand π ℓ₀ χ x y)) μ := by
  have h : formIntegrand π ℓ₀ χ x y =
      fun g => coeff π ℓ₀ x g * (conj (coeff π ℓ₀ y g) * (weight χ g : ℂ)) := by
    funext g
    simp only [formIntegrand, mul_assoc]
  rw [h]
  exact integrable_levelSet_coeff_mul μ π ℓ₀ hn hπ hℓ₀ x j
    (continuous_conj_coeff_mul_weight π ℓ₀ χ hπ.1.1 y)

theorem integrable_window_formIntegrand (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ₀ : IsSmoothVector π.dual ℓ₀) (x y : V) :
    Integrable ((window detOrd n 0).indicator (formIntegrand π ℓ₀ χ x y)) μ := by
  refine (integrable_cutoffFun_mul μ π ℓ₀ hn hπ hℓ₀ x
    (continuous_conj_coeff_mul_weight π ℓ₀ χ hπ.1.1 y)).congr
    (Filter.Eventually.of_forall fun g => ?_)
  exact (window_formIntegrand_eq π ℓ₀ χ x y g).symm

/-- The Hermitian form
`B(x, y) = ∫_{0 ≤ ord det < n} ℓ₀(π(g⁻¹) x) \overline{ℓ₀(π(g⁻¹) y)} r^{ord det g} dμ(g)`. -/
def form (x y : V) : ℂ :=
  ∫ g, (window detOrd n 0).indicator (formIntegrand π ℓ₀ χ x y) g ∂μ

/-- **Quasi-invariance.** `B(π(h) x, π(h) y) = r^{ord det h} B(x, y)`. -/
theorem form_rho (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ₀ : IsSmoothVector π.dual ℓ₀) (hπχ : HasCentralCharacterRep π χ)
    (h : GeneralLinear n F) (x y : V) :
    form π ℓ₀ χ μ (π h x) (π h y) = (weight χ h : ℂ) * form π ℓ₀ χ μ x y := by
  have hΦ : ∀ g, formIntegrand π ℓ₀ χ x y (centralUniformizer * g) =
      formIntegrand π ℓ₀ χ x y g := formIntegrand_central π ℓ₀ χ hn hπχ x y
  have key := integral_window_comp_mul_left μ detOrd_mul
    (detOrd_centralUniformizer (F := F) (n := n)) hΦ
    (integrable_levelSet_formIntegrand π ℓ₀ χ μ hn hπ hℓ₀ x y) h⁻¹
  have hpt : ∀ g, (window detOrd n 0).indicator (formIntegrand π ℓ₀ χ (π h x) (π h y)) g =
      (weight χ h : ℂ) *
        (window detOrd n 0).indicator (fun g => formIntegrand π ℓ₀ χ x y (h⁻¹ * g)) g := by
    intro g
    by_cases hg : g ∈ window detOrd n 0
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, formIntegrand_rho]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, mul_zero]
  unfold form
  simp_rw [hpt]
  rw [integral_const_mul, key]

omit [T2Space (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)] [μ.IsHaarMeasure] in
/-- **Hermitian symmetry.** `B(y, x) = \overline{B(x, y)}`. -/
theorem form_swap (x y : V) : form π ℓ₀ χ μ y x = conj (form π ℓ₀ χ μ x y) := by
  unfold form
  rw [← integral_conj]
  congr 1
  funext g
  by_cases hg : g ∈ window detOrd n 0
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
    simp only [formIntegrand, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, map_zero]

theorem form_add_left (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ₀ : IsSmoothVector π.dual ℓ₀) (x x' y : V) :
    form π ℓ₀ χ μ (x + x') y = form π ℓ₀ χ μ x y + form π ℓ₀ χ μ x' y := by
  unfold form
  rw [← integral_add (integrable_window_formIntegrand π ℓ₀ χ μ hn hπ hℓ₀ x y)
    (integrable_window_formIntegrand π ℓ₀ χ μ hn hπ hℓ₀ x' y)]
  congr 1
  funext g
  by_cases hg : g ∈ window detOrd n 0
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, Set.indicator_of_mem hg]
    simp only [formIntegrand, coeff_add]
    ring
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, Set.indicator_of_notMem hg,
      add_zero]

omit [T2Space (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)] [μ.IsHaarMeasure] in
theorem form_smul_left (c : ℂ) (x y : V) :
    form π ℓ₀ χ μ (c • x) y = c * form π ℓ₀ χ μ x y := by
  unfold form
  rw [← integral_const_mul]
  congr 1
  funext g
  by_cases hg : g ∈ window detOrd n 0
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
    simp only [formIntegrand, coeff_smul]
    ring
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, mul_zero]

/-- The density of `B(s, s)`: `1[0 ≤ ord det g < n] ‖ℓ₀(π(g⁻¹) s)‖² r^{ord det g}`. -/
def selfDensity (s : V) (g : GeneralLinear n F) : ℝ :=
  (window detOrd n 0).indicator (fun g => ‖coeff π ℓ₀ s g‖ ^ 2 * weight χ g) g

omit [T2Space (GeneralLinear n F)] [MeasurableSpace (GeneralLinear n F)]
  [BorelSpace (GeneralLinear n F)] in
theorem window_formIntegrand_self (s : V) (g : GeneralLinear n F) :
    (window detOrd n 0).indicator (formIntegrand π ℓ₀ χ s s) g =
      (selfDensity π ℓ₀ χ s g : ℂ) := by
  by_cases hg : g ∈ window detOrd n 0
  · rw [Set.indicator_of_mem hg, selfDensity, Set.indicator_of_mem hg]
    simp only [formIntegrand, Complex.mul_conj']
    push_cast
    ring
  · rw [Set.indicator_of_notMem hg, selfDensity, Set.indicator_of_notMem hg,
      Complex.ofReal_zero]

omit [T2Space (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)] [μ.IsHaarMeasure] in
theorem form_self (s : V) :
    form π ℓ₀ χ μ s s = ((∫ g, selfDensity π ℓ₀ χ s g ∂μ : ℝ) : ℂ) := by
  unfold form
  simp_rw [window_formIntegrand_self]
  exact integral_ofReal

omit [T2Space (GeneralLinear n F)] [MeasurableSpace (GeneralLinear n F)]
  [BorelSpace (GeneralLinear n F)] in
theorem one_mem_window (hn : 0 < n) : (1 : GeneralLinear n F) ∈ window detOrd n 0 := by
  rw [mem_window, detOrd_one]
  constructor <;> omega

/-- **Positivity.** `B(s, s) > 0` when `ℓ₀(s) ≠ 0`. -/
theorem integral_selfDensity_pos (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ₀ : IsSmoothVector π.dual ℓ₀) (s : V) (hs : ℓ₀ s ≠ 0) :
    0 < ∫ g, selfDensity π ℓ₀ χ s g ∂μ := by
  have hlc : IsLocallyConstant (selfDensity π ℓ₀ χ s) :=
    isLocallyConstant_indicator_detOrd (fun d => 0 ≤ d ∧ d < 0 + n)
      ((isLocallyConstant_coeff π ℓ₀ hπ.1.1 s).comp₂ (isLocallyConstant_weight χ)
        (fun (c : ℂ) (w : ℝ) => ‖c‖ ^ 2 * w))
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hlc.continuous
    ((hasCompactSupport_cutoffFun π ℓ₀ hn hπ hℓ₀ s).mono ?_) ?_ ?_
  · intro g hg
    rw [Function.mem_support] at hg ⊢
    by_cases hw : g ∈ window detOrd n 0
    · rw [selfDensity, Set.indicator_of_mem hw] at hg
      rw [cutoffFun, Set.indicator_of_mem hw]
      intro h0
      rw [h0, norm_zero] at hg
      simp at hg
    · rw [selfDensity, Set.indicator_of_notMem hw] at hg
      exact absurd rfl hg
  · intro g
    exact Set.indicator_nonneg (fun g _ => mul_nonneg (sq_nonneg _) (weight_pos χ g).le) g
  · rw [selfDensity, Set.indicator_of_mem (one_mem_window hn),
      weight_of_detOrd_eq_zero χ detOrd_one, mul_one]
    simp only [coeff, inv_one, map_one, Module.End.one_apply]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hs)

/-- The smooth linear form `x ↦ B(x, s)`. -/
def formDual (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ₀ : IsSmoothVector π.dual ℓ₀) (s : V) : Module.Dual ℂ V where
  toFun x := form π ℓ₀ χ μ x s
  map_add' x x' := form_add_left π ℓ₀ χ μ hn hπ hℓ₀ x x' s
  map_smul' c x := form_smul_left π ℓ₀ χ μ c x s

@[simp]
theorem formDual_apply (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ₀ : IsSmoothVector π.dual ℓ₀) (s x : V) :
    formDual π ℓ₀ χ μ hn hπ hℓ₀ s x = form π ℓ₀ χ μ x s := rfl

/-- `x ↦ B(x, s)` is fixed by the open subgroup of determinant-unit elements fixing `s`. -/
theorem isSmoothVector_formDual (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ₀ : IsSmoothVector π.dual ℓ₀) (hπχ : HasCentralCharacterRep π χ) (s : V) :
    IsSmoothVector π.dual (formDual π ℓ₀ χ μ hn hπ hℓ₀ s) := by
  obtain ⟨K₁, hK₁⟩ := hπ.1.1 s
  let K₀ : OpenSubgroup (GeneralLinear n F) :=
    ⟨((⟨⟩ : LocalFieldData F).determinantNorm n).ker,
      (⟨⟩ : LocalFieldData F).isOpen_ker_determinantNorm n⟩
  refine ⟨K₁ ⊓ K₀, ?_⟩
  rintro ⟨k, hk⟩
  have hk' : k ∈ K₁.toSubgroup ⊓ K₀.toSubgroup := hk
  rw [Subgroup.mem_inf] at hk'
  have hk₀ : detOrd k = 0 := (mem_ker_determinantNorm_iff k).mp hk'.2
  have hs : π k⁻¹ s = s := hK₁ ⟨k⁻¹, K₁.toSubgroup.inv_mem hk'.1⟩
  apply LinearMap.ext
  intro x
  change form π ℓ₀ χ μ (π k⁻¹ x) s = form π ℓ₀ χ μ x s
  calc form π ℓ₀ χ μ (π k⁻¹ x) s = form π ℓ₀ χ μ (π k⁻¹ x) (π k⁻¹ s) := by rw [hs]
    _ = (weight χ k⁻¹ : ℂ) * form π ℓ₀ χ μ x s := form_rho π ℓ₀ χ μ hn hπ hℓ₀ hπχ k⁻¹ x s
    _ = form π ℓ₀ χ μ x s := by
      rw [weight_of_detOrd_eq_zero χ (by rw [detOrd_inv, hk₀, neg_zero]), Complex.ofReal_one,
        one_mul]

theorem form_rho_inv_self (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ₀ : IsSmoothVector π.dual ℓ₀) (hπχ : HasCentralCharacterRep π χ) (s : V)
    (g : GeneralLinear n F) :
    form π ℓ₀ χ μ (π g⁻¹ s) s = ((weight χ g : ℂ))⁻¹ * conj (form π ℓ₀ χ μ (π g s) s) := by
  have h := form_rho π ℓ₀ χ μ hn hπ hℓ₀ hπχ g (π g⁻¹ s) s
  have hgg : π g (π g⁻¹ s) = s := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hgg, form_swap π ℓ₀ χ μ (π g s) s] at h
  have hw : (weight χ g : ℂ) ≠ 0 := by exact_mod_cast (weight_pos χ g).ne'
  rw [h, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]

/-- The density `1[0 ≤ ord det g < n] r^{-ord det g} ‖B(π(g) s, s)‖²`. -/
def crossDensity (s : V) (g : GeneralLinear n F) : ℝ :=
  (window detOrd n 0).indicator (fun g => (weight χ g)⁻¹ * ‖form π ℓ₀ χ μ (π g s) s‖ ^ 2) g

/-- **Nonvanishing of the Schur constant.** For `ℓ = B(·, s)` with `ℓ₀(s) ≠ 0`,
`∫ f_s(g) ℓ(π(g) s) dμ(g) ≠ 0`, where `f_s` is the cut-off coefficient of `s` against `ℓ`. -/
theorem integral_cutoff_formDual_ne_zero (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ₀ : IsSmoothVector π.dual ℓ₀) (hπχ : HasCentralCharacterRep π χ) (s : V)
    (hs : ℓ₀ s ≠ 0) :
    ∫ g, cutoffFun π (formDual π ℓ₀ χ μ hn hπ hℓ₀ s) s g *
      formDual π ℓ₀ χ μ hn hπ hℓ₀ s (π g s) ∂μ ≠ 0 := by
  set ℓ := formDual π ℓ₀ χ μ hn hπ hℓ₀ s with hℓdef
  have hℓ : IsSmoothVector π.dual ℓ := isSmoothVector_formDual π ℓ₀ χ μ hn hπ hℓ₀ hπχ s
  have hcoeff : ∀ g, coeff π ℓ s g =
      ((weight χ g : ℂ))⁻¹ * conj (form π ℓ₀ χ μ (π g s) s) := by
    intro g
    exact form_rho_inv_self π ℓ₀ χ μ hn hπ hℓ₀ hπχ s g
  have hpt : ∀ g, cutoffFun π ℓ s g * ℓ (π g s) = (crossDensity π ℓ₀ χ μ s g : ℂ) := by
    intro g
    by_cases hg : g ∈ window detOrd n 0
    · rw [cutoffFun, Set.indicator_of_mem hg, crossDensity, Set.indicator_of_mem hg, hcoeff,
        formDual_apply, mul_assoc, Complex.conj_mul']
      push_cast
      ring
    · rw [cutoffFun, Set.indicator_of_notMem hg, crossDensity, Set.indicator_of_notMem hg,
        zero_mul, Complex.ofReal_zero]
  simp_rw [hpt]
  rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
  apply ne_of_gt
  have hlc : IsLocallyConstant (crossDensity π ℓ₀ χ μ s) :=
    isLocallyConstant_indicator_detOrd (fun d => 0 ≤ d ∧ d < 0 + n)
      ((isLocallyConstant_weight χ).comp₂
        ((Hecke.orbitMap_locallyConstant π (hπ.1.1 s)).comp fun v => ℓ v)
        (fun (w : ℝ) (c : ℂ) => w⁻¹ * ‖c‖ ^ 2))
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hlc.continuous
    ((hasCompactSupport_cutoffFun π ℓ hn hπ hℓ s).mono ?_) ?_ ?_
  · intro g hg
    rw [Function.mem_support] at hg ⊢
    by_cases hw : g ∈ window detOrd n 0
    · rw [crossDensity, Set.indicator_of_mem hw] at hg
      rw [cutoffFun, Set.indicator_of_mem hw, hcoeff]
      have hβ : form π ℓ₀ χ μ (π g s) s ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hg
        simp at hg
      have hw' : (weight χ g : ℂ) ≠ 0 := by exact_mod_cast (weight_pos χ g).ne'
      exact mul_ne_zero (inv_ne_zero hw') ((map_ne_zero _).mpr hβ)
    · rw [crossDensity, Set.indicator_of_notMem hw] at hg
      exact absurd rfl hg
  · intro g
    exact Set.indicator_nonneg
      (fun g _ => mul_nonneg (inv_nonneg.mpr (weight_pos χ g).le) (sq_nonneg _)) g
  · rw [crossDensity, Set.indicator_of_mem (one_mem_window hn),
      weight_of_detOrd_eq_zero χ detOrd_one, inv_one, one_mul, map_one, Module.End.one_apply,
      form_self]
    have hpos := integral_selfDensity_pos π ℓ₀ χ μ hn hπ hℓ₀ s hs
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact pow_ne_zero 2 (abs_ne_zero.mpr hpos.ne')

end Form

section Main

variable [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
  [TotallyDisconnectedSpace (GeneralLinear n F)] [MeasurableSpace (GeneralLinear n F)]
  [BorelSpace (GeneralLinear n F)] (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- **Pseudo-coefficients with vanishing constant terms.** For an irreducible supercuspidal
`π` of `GL_n(F)`, `0 < n`, with central character `χ`, and a Haar measure `μ`, there is a
Schwartz–Bruhat `f` with vanishing constant terms, `tr π(f) = 1` and `tr ρ(f) = 0` for every
irreducible admissible `ρ ≇ π` with central character `χ`. -/
theorem exists_cuspForm_pseudoCoefficient (hn : 0 < n)
    (π : Representation ℂ (GeneralLinear n F) V) (hπ : GeneralLinear.IsSupercuspidal π)
    (hirr : π.IsIrreducible) {χ : Subgroup.center (GeneralLinear n F) →* ℂˣ}
    (hπχ : HasCentralCharacterRep π χ) :
    ∃ f : SchwartzBruhat (GeneralLinear n F),
      HasVanishingConstantTerms (f : GeneralLinear n F → ℂ) ∧
      Character.distribution μ π hπ.1 f = 1 ∧
      ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (ρ : Representation ℂ (GeneralLinear n F) W) (hρ : IsAdmissible ρ),
        ρ.IsIrreducible → HasCentralCharacterRep ρ χ → IsEmpty (ρ.Equiv π) →
        Character.distribution μ ρ hρ f = 0 := by
  let := hirr
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F))
    π.asModule
  obtain ⟨s, hs⟩ := exists_ne (0 : V)
  obtain ⟨ℓ₀, hℓ₀, -, hℓ₀s⟩ := CompactCoefficientSemisimplicity.exists_smooth_dual_separating
    π hπ.1.1 ⊥ (a := s) (by
      change s ∉ (⊥ : Submodule ℂ V)
      simpa only [Submodule.mem_bot] using hs)
  let ℓ := formDual π ℓ₀ χ μ hn hπ hℓ₀ s
  have hℓ : IsSmoothVector π.dual ℓ := isSmoothVector_formDual π ℓ₀ χ μ hn hπ hℓ₀ hπχ s
  have hI := integral_cutoff_formDual_ne_zero π ℓ₀ χ μ hn hπ hℓ₀ hπχ s hℓ₀s
  obtain ⟨c, hc⟩ := exists_integratedAction_cutoff_self μ π ℓ hn hπ hirr hℓ hπχ
  have hcs : c s ≠ 0 := by
    intro h0
    have h := Hecke.integratedAction_dual μ π hπ.1.1 (cutoff π ℓ hn hπ hℓ s) s ℓ
    rw [hc, h0, zero_smul, map_zero] at h
    exact hI h.symm
  refine ⟨(c s)⁻¹ • cutoff π ℓ hn hπ hℓ s, ?_, ?_, ?_⟩
  · exact (hasVanishingConstantTerms_cutoff π ℓ hn hπ hℓ s).const_mul (c s)⁻¹
  · rw [map_smul, distribution_cutoff_self μ π ℓ hn hπ hℓ hc hs, smul_eq_mul,
      inv_mul_cancel₀ hcs]
  · intro W _ _ ρ hρ hρirr hρχ hne
    rw [map_smul, distribution_cutoff_eq_zero μ π ℓ hn hπ hirr hℓ hπχ ρ hρ hρirr hρχ hne s,
      smul_zero]

end Main

end Langlands.BaseChange.SupercuspidalCutoff
