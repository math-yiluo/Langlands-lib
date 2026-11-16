import Langlands.Global.RankinSelberg.EqualAnalyticRationalRows

/-! # The Eisenstein series as an integral of a theta series

For `g ∈ GL_n(𝔸)`, `n = r + 1`, the Eisenstein series of `EqualIntegrals` is
`E(g, Φ; s, χ) = Σ_(γ ∈ P'(F) \ GL_n(F)) |det γg|^s ∫_(𝔸^×) Φ(a e_n γ g) |a|^(ns) χ(a) d^×a`.
Writing `∫_(𝔸^×) = ∫_(D₁) Σ_(F^×)` and using `P'(F) \ GL_n(F) × F^× ≃ F^n ∖ 0`:

* `Σ_γ ∫_(𝔸^×) |Φ(a e_n γ g)| W(a) d^×a = ∫_(D₁) W(a) Θ⁺(Φ, ζ(a) g) d^×a` for every `F^×`-invariant
  weight `W ≥ 0` (`tsum_lintegral_section`);
* if the right side is finite for `W = |w|`, the same identity holds with `Φ`, `w` and `Θ`
  (`tsum_integral_section`);
* hence `E(g) = |det g|^s ∫_(D₁) |a|^(ns) χ(a) Θ(Φ, ζ(a) g) d^×a` and
  `|E(g)| ≤ |det g|^σ ∫_(D₁) ||a|^(ns) χ(a)| Θ⁺(Φ, ζ(a) g) d^×a`
  (`eisensteinSeries_eq`, `enorm_eisensteinSeries_le`).
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global
open scoped CategoryTheory.MonObj Matrix ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance eisSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance eisSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local notation "E" => GeneralLinearGroupPoints.adelicEquiv F

instance countable_units : Countable Fˣ := by
  have := numberField_countable F
  exact Units.val_injective.countable

instance countable_rationalGL (n : ℕ) : Countable (RationalGL F n) := by
  have := numberField_countable F
  have : Countable (Matrix (Fin n) (Fin n) F) := inferInstanceAs (Countable (Fin n → Fin n → F))
  exact Units.val_injective.countable

instance countable_parabolicCosets (r : ℕ) :
    Countable (LeftCosetSpace (eisensteinParabolic F r)) :=
  (LeftCosetSpace.mk_surjective _).countable

theorem summable_of_tsum_enorm_ne_top {J : Type*} {f : J → ℂ} (h : ∑' i, ‖f i‖ₑ ≠ ⊤) :
    Summable f := by
  refine Summable.of_norm ?_
  have h' : Summable fun i => ‖f i‖₊ := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa only [enorm_eq_nnnorm] using h
  exact NNReal.summable_coe.2 h'

/-! ### Unfolding `𝔸^× = F^× D₁` -/

theorem lintegral_idele_unfold (h : Points F 1 → ℝ≥0∞) :
    ∫⁻ z, h z ∂ideleMeasure F =
      ∑' f : Fˣ, ∫⁻ z in ideleDomain F, h (ratUnit F f * z) ∂ideleMeasure F := by
  rw [(isFundamentalDomain_ideleDomain F (ideleMeasure F)).lintegral_eq_tsum'' h,
    ← (ratUnitEquiv F).tsum_eq]
  rfl

theorem integral_idele_unfold (h : Points F 1 → ℂ) (hh : Integrable h (ideleMeasure F)) :
    ∫ z, h z ∂ideleMeasure F =
      ∑' f : Fˣ, ∫ z in ideleDomain F, h (ratUnit F f * z) ∂ideleMeasure F := by
  rw [(isFundamentalDomain_ideleDomain F (ideleMeasure F)).integral_eq_tsum'' h hh,
    ← (ratUnitEquiv F).tsum_eq]
  rfl

variable (r : ℕ)

theorem thetaNorm_eq_tsum_subtype (Φ : RowVector F (r + 1) → ℂ) (M : AdelicGL F (r + 1)) :
    thetaNorm F (r + 1) Φ M = ∑' C : {C : RatRow F (r + 1) // C ≠ 0},
      ‖Φ (ratRow F (r + 1) C * (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)))‖ₑ := by
  rw [thetaNorm]
  symm
  refine (tsum_subtype {C : RatRow F (r + 1) | C ≠ 0} (fun C =>
    ‖Φ (ratRow F (r + 1) C * (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)))‖ₑ)).trans ?_
  refine tsum_congr fun C => ?_
  by_cases hC : C = 0
  · simp [hC]
  · rw [Set.indicator_of_mem (show C ∈ {C : RatRow F (r + 1) | C ≠ 0} from hC)]
    simp only [hC, ↓reduceIte]

theorem thetaSum_eq_tsum_subtype (Φ : RowVector F (r + 1) → ℂ) (M : AdelicGL F (r + 1)) :
    thetaSum F (r + 1) Φ M = ∑' C : {C : RatRow F (r + 1) // C ≠ 0},
      Φ (ratRow F (r + 1) C * (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F))) := by
  rw [thetaSum]
  symm
  refine (tsum_subtype {C : RatRow F (r + 1) | C ≠ 0} (fun C =>
    Φ (ratRow F (r + 1) C * (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F))))).trans ?_
  refine tsum_congr fun C => ?_
  by_cases hC : C = 0
  · simp [hC]
  · rw [Set.indicator_of_mem (show C ∈ {C : RatRow F (r + 1) | C ≠ 0} from hC)]
    simp only [hC, ↓reduceIte]

/-- The function `a ↦ Φ(a e_n γ g)` of an idele. -/
def sectionRow (Φ : RowVector F (r + 1) → ℂ) (c : RationalGL F (r + 1)) (g : Points F (r + 1))
    (z : Points F 1) : ℂ :=
  Φ ((ideleOf F z : Adeles F) • lastRow F r (rationalPoint F (r + 1) c * g))

theorem continuous_sectionRow {Φ : RowVector F (r + 1) → ℂ} (hΦ : Continuous Φ)
    (c : RationalGL F (r + 1)) (g : Points F (r + 1)) : Continuous (sectionRow F r Φ c g) :=
  hΦ.comp ((Units.continuous_val.comp (continuous_ideleOf F)).smul continuous_const)

theorem sectionRow_ratUnit_mul (Φ : RowVector F (r + 1) → ℂ) (c : RationalGL F (r + 1))
    (g : Points F (r + 1)) (f : Fˣ) (z : Points F 1) :
    sectionRow F r Φ c g (ratUnit F f * z) = Φ (ratRow F (r + 1) ((f : F) • rowOf F r c) *
      (E (r + 1) (zeta F (r + 1) z * g) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F))) := by
  rw [sectionRow, ideleOf_smul_lastRow]

/-- **The `[0, ∞]` unfolding of the Eisenstein sum.** -/
theorem tsum_lintegral_section {Φ : RowVector F (r + 1) → ℂ} (hΦ : Continuous Φ)
    (W : Points F 1 → ℝ≥0∞) (hW : Measurable W) (hWinv : ∀ f z, W (ratUnit F f * z) = W z)
    (g : Points F (r + 1)) :
    ∑' q : LeftCosetSpace (eisensteinParabolic F r),
        ∫⁻ z, ‖sectionRow F r Φ (Quotient.out q) g z‖ₑ * W z ∂ideleMeasure F =
      ∫⁻ z in ideleDomain F, W z * thetaNorm F (r + 1) Φ (E (r + 1) (zeta F (r + 1) z * g))
        ∂ideleMeasure F := by
  have hm : ∀ q : LeftCosetSpace (eisensteinParabolic F r), Measurable fun z =>
      ‖sectionRow F r Φ (Quotient.out q) g z‖ₑ * W z := fun q =>
    (continuous_sectionRow F r hΦ _ g).measurable.enorm.mul hW
  calc ∑' q : LeftCosetSpace (eisensteinParabolic F r),
        ∫⁻ z, ‖sectionRow F r Φ (Quotient.out q) g z‖ₑ * W z ∂ideleMeasure F
      = ∑' q : LeftCosetSpace (eisensteinParabolic F r), ∫⁻ z in ideleDomain F,
          ∑' f : Fˣ, ‖sectionRow F r Φ (Quotient.out q) g (ratUnit F f * z)‖ₑ *
            W (ratUnit F f * z) ∂ideleMeasure F := by
        refine tsum_congr fun q => ?_
        rw [lintegral_idele_unfold F]
        exact (lintegral_tsum fun f =>
          ((hm q).comp (measurable_const_mul (ratUnit F f))).aemeasurable).symm
    _ = ∫⁻ z in ideleDomain F, ∑' q : LeftCosetSpace (eisensteinParabolic F r),
          ∑' f : Fˣ, ‖sectionRow F r Φ (Quotient.out q) g (ratUnit F f * z)‖ₑ *
            W (ratUnit F f * z) ∂ideleMeasure F := by
        exact (lintegral_tsum fun q => (StronglyMeasurable.tsum fun f =>
          ((hm q).comp (measurable_const_mul (ratUnit F f))).stronglyMeasurable).measurable.aemeasurable).symm
    _ = ∫⁻ z in ideleDomain F, W z * thetaNorm F (r + 1) Φ (E (r + 1) (zeta F (r + 1) z * g))
          ∂ideleMeasure F := by
        refine lintegral_congr fun z => ?_
        simp only [hWinv, sectionRow_ratUnit_mul]
        rw [← ENNReal.tsum_prod, thetaNorm_eq_tsum_subtype, ← (cosetRowEquiv F r).tsum_eq,
          ← ENNReal.tsum_mul_left]
        refine tsum_congr fun p => ?_
        rw [cosetRowEquiv_apply, mul_comm]

/-- **The complex unfolding of the Eisenstein sum.** -/
theorem tsum_integral_section {Φ : RowVector F (r + 1) → ℂ} (hΦ : Continuous Φ)
    (w : Points F 1 → ℂ) (hw : Continuous w) (hwinv : ∀ f z, w (ratUnit F f * z) = w z)
    (g : Points F (r + 1))
    (hfin : ∫⁻ z in ideleDomain F, ‖w z‖ₑ *
      thetaNorm F (r + 1) Φ (E (r + 1) (zeta F (r + 1) z * g)) ∂ideleMeasure F ≠ ⊤) :
    ∑' q : LeftCosetSpace (eisensteinParabolic F r),
        ∫ z, sectionRow F r Φ (Quotient.out q) g z * w z ∂ideleMeasure F =
      ∫ z in ideleDomain F, w z * thetaSum F (r + 1) Φ (E (r + 1) (zeta F (r + 1) z * g))
        ∂ideleMeasure F := by
  set Q := LeftCosetSpace (eisensteinParabolic F r)
  -- the unfolded terms
  set a : Q × Fˣ → Points F 1 → ℂ := fun p z =>
    sectionRow F r Φ (Quotient.out p.1) g (ratUnit F p.2 * z) * w z with ha
  have hcont : ∀ p : Q × Fˣ, Continuous (a p) := fun p =>
    ((continuous_sectionRow F r hΦ _ g).comp (continuous_const.mul continuous_id)).mul hw
  have hm : ∀ q : Q, Measurable fun z => ‖sectionRow F r Φ (Quotient.out q) g z‖ₑ * ‖w z‖ₑ :=
    fun q => (continuous_sectionRow F r hΦ _ g).measurable.enorm.mul hw.measurable.enorm
  have hsum := tsum_lintegral_section F r hΦ (fun z => ‖w z‖ₑ) hw.measurable.enorm
    (fun f z => by simp only [hwinv]) g
  -- the double sum of the norms is finite
  have hnorm : ∑' p : Q × Fˣ, ∫⁻ z in ideleDomain F, ‖a p z‖ₑ ∂ideleMeasure F ≠ ⊤ := by
    rw [ENNReal.tsum_prod']
    have h1 : ∀ q : Q, ∑' f : Fˣ, ∫⁻ z in ideleDomain F, ‖a (q, f) z‖ₑ ∂ideleMeasure F =
        ∫⁻ z, ‖sectionRow F r Φ (Quotient.out q) g z‖ₑ * ‖w z‖ₑ ∂ideleMeasure F := by
      intro q
      rw [lintegral_idele_unfold F]
      refine tsum_congr fun f => lintegral_congr fun z => ?_
      simp only [ha, enorm_mul, hwinv]
    simp only [h1]
    rw [hsum]
    exact hfin
  have hint : ∀ q : Q, Integrable (fun z => sectionRow F r Φ (Quotient.out q) g z * w z)
      (ideleMeasure F) := by
    intro q
    refine ⟨((continuous_sectionRow F r hΦ _ g).mul hw).aestronglyMeasurable, ?_⟩
    have h2 : ∫⁻ z, ‖sectionRow F r Φ (Quotient.out q) g z * w z‖ₑ ∂ideleMeasure F ≤
        ∑' q' : Q, ∫⁻ z, ‖sectionRow F r Φ (Quotient.out q') g z‖ₑ * ‖w z‖ₑ ∂ideleMeasure F := by
      simp only [enorm_mul]
      exact ENNReal.le_tsum (f := fun q' : Q =>
        ∫⁻ z, ‖sectionRow F r Φ (Quotient.out q') g z‖ₑ * ‖w z‖ₑ ∂ideleMeasure F) q
    rw [hsum] at h2
    exact lt_of_le_of_lt h2 (lt_top_iff_ne_top.2 hfin)
  have hb : Summable fun p : Q × Fˣ => ∫ z in ideleDomain F, a p z ∂ideleMeasure F := by
    refine summable_of_tsum_enorm_ne_top (ne_top_of_le_ne_top hnorm ?_)
    exact ENNReal.tsum_le_tsum fun p => enorm_integral_le_lintegral_enorm _
  calc ∑' q : Q, ∫ z, sectionRow F r Φ (Quotient.out q) g z * w z ∂ideleMeasure F
      = ∑' q : Q, ∑' f : Fˣ, ∫ z in ideleDomain F, a (q, f) z ∂ideleMeasure F := by
        refine tsum_congr fun q => ?_
        rw [integral_idele_unfold F _ (hint q)]
        refine tsum_congr fun f => integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [ha, hwinv]
    _ = ∑' p : Q × Fˣ, ∫ z in ideleDomain F, a p z ∂ideleMeasure F :=
        (hb.tsum_prod' fun q => hb.prod_factor q).symm
    _ = ∫ z in ideleDomain F, ∑' p : Q × Fˣ, a p z ∂ideleMeasure F :=
        (integral_tsum (fun p => (hcont p).aestronglyMeasurable) hnorm).symm
    _ = ∫ z in ideleDomain F, w z * thetaSum F (r + 1) Φ (E (r + 1) (zeta F (r + 1) z * g))
          ∂ideleMeasure F := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [ha, sectionRow_ratUnit_mul]
        rw [tsum_mul_right, thetaSum_eq_tsum_subtype, ← (cosetRowEquiv F r).tsum_eq, mul_comm]
        rfl

/-! ### The Eisenstein series -/

variable {F}

/-- The weight `w_s(a) = |a|^(ns) χ(a)` of the section. -/
def sectionWeight (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (s : ℂ) (z : Points F 1) : ℂ :=
  detPower F 1 z ((r + 1 : ℂ) * s) * ideleChar F χ z

variable (F)

theorem continuous_sectionWeight (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (s : ℂ) :
    Continuous (sectionWeight (F := F) r χ s) :=
  (UnequalAnalytic.continuous_detPower F 1 _).mul (continuous_ideleChar F χ)

theorem sectionWeight_ratUnit_mul (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (s : ℂ) (f : Fˣ)
    (z : Points F 1) : sectionWeight (F := F) r χ s (ratUnit F f * z) =
      sectionWeight (F := F) r χ s z := by
  have h1 : detNorm F 1 (ratUnit F f * z) = detNorm F 1 z :=
    detNorm_ideleRational_mul F ⟨ratUnit F f, ratUnit_mem F f⟩ z
  have h2 : ideleChar F χ (ratUnit F f * z) = ideleChar F χ z :=
    ideleChar_ideleRational_mul F χ ⟨ratUnit F f, ratUnit_mem F f⟩ z
  simp only [sectionWeight, detPower, h1, h2]

theorem eisensteinSectionIntegrand_eq (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) (c : RationalGL F (r + 1)) (g : Points F (r + 1))
    (z : Points F 1) :
    eisensteinSectionIntegrand F χ Φ s (rationalPoint F (r + 1) c * g) z =
      sectionRow F r Φ c g z * sectionWeight (F := F) r χ s z := by
  simp only [eisensteinSectionIntegrand, sectionRow, sectionWeight, ideleChar, mul_assoc]

theorem detPower_rationalPoint_mul (c : RationalGL F (r + 1)) (g : Points F (r + 1)) (s : ℂ) :
    detPower F (r + 1) (rationalPoint F (r + 1) c * g) s = detPower F (r + 1) g s :=
  UnequalAnalytic.detPower_rational_mul F _ g s

/-- **The Eisenstein series as an integral of the theta series.** -/
theorem eisensteinSeries_eq (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : Continuous Φ) (s : ℂ) (g : Points F (r + 1))
    (hfin : ∫⁻ z in ideleDomain F, ‖sectionWeight (F := F) r χ s z‖ₑ *
      thetaNorm F (r + 1) Φ (E (r + 1) (zeta F (r + 1) z * g)) ∂ideleMeasure F ≠ ⊤) :
    eisensteinSeries F χ Φ s g = detPower F (r + 1) g s *
      ∫ z in ideleDomain F, sectionWeight (F := F) r χ s z *
        thetaSum F (r + 1) Φ (E (r + 1) (zeta F (r + 1) z * g)) ∂ideleMeasure F := by
  rw [← tsum_integral_section F r hΦ _ (continuous_sectionWeight F r χ s)
    (sectionWeight_ratUnit_mul F r χ s) g hfin, ← tsum_mul_left]
  unfold eisensteinSeries eisensteinSection
  refine tsum_congr fun q => ?_
  rw [detPower_rationalPoint_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact eisensteinSectionIntegrand_eq F r χ Φ s _ g z

/-- **A bound for the Eisenstein series.** -/
theorem enorm_eisensteinSeries_le (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : Continuous Φ) (s : ℂ) (g : Points F (r + 1)) :
    ‖eisensteinSeries F χ Φ s g‖ₑ ≤ ‖detPower F (r + 1) g s‖ₑ *
      ∫⁻ z in ideleDomain F, ‖sectionWeight (F := F) r χ s z‖ₑ *
        thetaNorm F (r + 1) Φ (E (r + 1) (zeta F (r + 1) z * g)) ∂ideleMeasure F := by
  rw [← tsum_lintegral_section F r hΦ _ (continuous_sectionWeight F r χ s).measurable.enorm
    (fun f z => by simp only [sectionWeight_ratUnit_mul]) g, ← ENNReal.tsum_mul_left]
  refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun q => ?_)
  unfold eisensteinSection
  rw [enorm_mul, detPower_rationalPoint_mul]
  gcongr
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun z => ?_))
  rw [eisensteinSectionIntegrand_eq, enorm_mul]

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
