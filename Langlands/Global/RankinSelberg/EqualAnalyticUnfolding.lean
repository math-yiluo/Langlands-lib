import Langlands.Global.RankinSelberg.EqualAnalyticEisensteinInvariance

/-! # Unfolding the equal-rank integral to the theta kernel

Let `P = φ φ'` be continuous, invariant under `GL_n(F)` and with `P(a g) = χ(a) P(g)` for scalar
ideles `a`, and let `Φ` be continuous. With the theta kernel
`K_s(g) = P(g) |det g|^s Θ(Φ, g)` and its majorant `K⁺_s(g) = |P(g)| ||det g|^s| Θ⁺(Φ, g)`:

if `∫_(GL_n(F)\GL_n(𝔸)) K⁺_s < ∞`, then the integrand `φ φ' E(·, Φ; s, χ)` of `equalIntegral` is
integrable on `Z_n(𝔸) GL_n(F) \ GL_n(𝔸)` and
`I(s; φ, φ', Φ) = ∫_(GL_n(F)\GL_n(𝔸)) K_s` (`equalIntegral_unfold`).

The proof combines the fibration of `GL_n(F)\GL_n(𝔸)` over the centre with the expression of
`E` as an integral of the theta series over `F^× \ 𝔸^×`.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global
open scoped CategoryTheory.MonObj Matrix ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance unfSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unfSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

local notation "E" => GeneralLinearGroupPoints.adelicEquiv F
local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph F

/-- The theta kernel `K_s(g) = P(g) |det g|^s Θ(Φ, g)`. -/
def thetaKernel (P : Points F (r + 1) → ℂ) (Φ : RowVector F (r + 1) → ℂ) (s : ℂ)
    (g : Points F (r + 1)) : ℂ :=
  P g * detPower F (r + 1) g s * thetaSum F (r + 1) Φ (E (r + 1) g)

/-- The majorant `K⁺_s(g) = |P(g)| ||det g|^s| Θ⁺(Φ, g)`. -/
def thetaKernelNorm (P : Points F (r + 1) → ℂ) (Φ : RowVector F (r + 1) → ℂ) (s : ℂ)
    (g : Points F (r + 1)) : ℝ≥0∞ :=
  ‖P g‖ₑ * ‖detPower F (r + 1) g s‖ₑ * thetaNorm F (r + 1) Φ (E (r + 1) g)

theorem enorm_thetaKernel_le (P : Points F (r + 1) → ℂ) (Φ : RowVector F (r + 1) → ℂ) (s : ℂ)
    (g : Points F (r + 1)) : ‖thetaKernel F r P Φ s g‖ₑ ≤ thetaKernelNorm F r P Φ s g := by
  rw [thetaKernel, thetaKernelNorm, enorm_mul, enorm_mul]
  gcongr
  exact enorm_thetaSum_le _ _ _

theorem adelicEquiv_rational_mul (c : RationalGroupPoints F (Scheme F (r + 1)))
    (g : Points F (r + 1)) :
    E (r + 1) (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) =
      AdelicGL.rational F (r + 1) (GeneralLinearGroupPoints.rationalEquiv F (r + 1) c) *
        E (r + 1) g := by
  rw [map_mul]
  exact congrArg (· * E (r + 1) g) (GeneralLinearGroupPoints.adelicHomeomorph_rational F _ c)

theorem thetaKernel_rational_mul {P : Points F (r + 1) → ℂ}
    (hP : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      P (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = P g)
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) (c : RationalGroupPoints F (Scheme F (r + 1)))
    (g : Points F (r + 1)) :
    thetaKernel F r P Φ s (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) =
      thetaKernel F r P Φ s g := by
  rw [thetaKernel, thetaKernel, hP, UnequalAnalytic.detPower_rational_mul,
    adelicEquiv_rational_mul, thetaSum_rational_mul]

theorem thetaKernelNorm_rational_mul {P : Points F (r + 1) → ℂ}
    (hP : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      P (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = P g)
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) (c : RationalGroupPoints F (Scheme F (r + 1)))
    (g : Points F (r + 1)) :
    thetaKernelNorm F r P Φ s (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) =
      thetaKernelNorm F r P Φ s g := by
  rw [thetaKernelNorm, thetaKernelNorm, hP, UnequalAnalytic.detPower_rational_mul,
    adelicEquiv_rational_mul, thetaNorm_rational_mul]

theorem glRational_invariant {Z : Type*} {f : Points F (r + 1) → Z}
    (hf : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      f (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = f g) :
    ∀ (c : glRational F (r + 1)) (g : Points F (r + 1)), f ((c : Points F (r + 1)) * g) = f g := by
  rintro ⟨_, c, rfl⟩ g
  exact hf c g

theorem thetaKernel_zeta_mul {P : Points F (r + 1) → ℂ} {χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hcent : ∀ (a : Points F 1) (g : Points F (r + 1)),
      P (zeta F (r + 1) a * g) = ideleChar F χ a * P g)
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) (a : Points F 1) (g : Points F (r + 1)) :
    thetaKernel F r P Φ s (zeta F (r + 1) a * g) = P g * detPower F (r + 1) g s *
      (sectionWeight (F := F) r χ s a *
        thetaSum F (r + 1) Φ (E (r + 1) (zeta F (r + 1) a * g))) := by
  rw [thetaKernel, hcent, detPower_zeta_mul, sectionWeight]
  ring

theorem thetaKernelNorm_zeta_mul {P : Points F (r + 1) → ℂ} {χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hcent : ∀ (a : Points F 1) (g : Points F (r + 1)),
      P (zeta F (r + 1) a * g) = ideleChar F χ a * P g)
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) (a : Points F 1) (g : Points F (r + 1)) :
    thetaKernelNorm F r P Φ s (zeta F (r + 1) a * g) = ‖P g‖ₑ * ‖detPower F (r + 1) g s‖ₑ *
      (‖sectionWeight (F := F) r χ s a‖ₑ *
        thetaNorm F (r + 1) Φ (E (r + 1) (zeta F (r + 1) a * g))) := by
  rw [thetaKernelNorm, hcent, detPower_zeta_mul, sectionWeight]
  simp only [enorm_mul]
  ring

theorem stronglyMeasurable_thetaKernel {P : Points F (r + 1) → ℂ} (hP : Continuous P)
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : Continuous Φ) (s : ℂ) :
    StronglyMeasurable (thetaKernel F r P Φ s) :=
  ((hP.mul (UnequalAnalytic.continuous_detPower F (r + 1) s)).stronglyMeasurable).mul
    (stronglyMeasurable_thetaSum F (r + 1) hΦ)

theorem measurable_thetaKernelNorm {P : Points F (r + 1) → ℂ} (hP : Continuous P)
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : Continuous Φ) (s : ℂ) :
    Measurable (thetaKernelNorm F r P Φ s) :=
  ((hP.measurable.enorm).mul (UnequalAnalytic.continuous_detPower F (r + 1) s).measurable.enorm).mul
    (measurable_thetaNorm F (r + 1) hΦ)

theorem continuous_lastRow : Continuous (lastRow F r) := by
  show Continuous fun g : Points F (r + 1) => (Matrix.of fun (_ : Fin 1) j =>
    ((e (r + 1) g : AdelicGL F (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F))
      (Fin.last r) j : RowVector F (r + 1))
  exact continuous_matrix fun _ j =>
    (Units.continuous_val.comp (e (r + 1)).continuous).matrix_elem (Fin.last r) j

theorem stronglyMeasurable_eisensteinSection (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : Continuous Φ) (s : ℂ) :
    StronglyMeasurable (eisensteinSection F χ Φ s) := by
  have hk : Continuous fun p : Points F (r + 1) × Points F 1 =>
      eisensteinSectionIntegrand F χ Φ s p.1 p.2 := by
    have h : (fun p : Points F (r + 1) × Points F 1 =>
        eisensteinSectionIntegrand F χ Φ s p.1 p.2) = fun p =>
        Φ ((ideleOf F p.2 : Adeles F) • lastRow F r p.1) * sectionWeight (F := F) r χ s p.2 :=
      funext fun p => eisensteinSectionIntegrand_eq' F r χ Φ s p.1 p.2
    rw [h]
    exact (hΦ.comp (((Units.continuous_val.comp (continuous_ideleOf F)).comp continuous_snd).smul
      ((continuous_lastRow F r).comp continuous_fst))).mul
      ((continuous_sectionWeight F r χ s).comp continuous_snd)
  exact (UnequalAnalytic.continuous_detPower F (r + 1) s).stronglyMeasurable.mul
    (hk.stronglyMeasurable.integral_prod_right' (ν := ideleMeasure F))

theorem stronglyMeasurable_eisensteinSeries (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : Continuous Φ) (s : ℂ) :
    StronglyMeasurable (eisensteinSeries F χ Φ s) := by
  refine StronglyMeasurable.tsum fun q => ?_
  exact (stronglyMeasurable_eisensteinSection F r χ hΦ s).comp_measurable
    (continuous_const.mul continuous_id).measurable

/-- **Unfolding.** -/
theorem equalIntegral_unfold [CompactSpace (AdeleQuotient F)]
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) {φ φ' : Points F (r + 1) → ℂ}
    (hφc : Continuous φ) (hφ'c : Continuous φ')
    (hφr : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      φ (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = φ g)
    (hφ'r : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      φ' (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = φ' g)
    (hcent : ∀ (a : Points F 1) (g : Points F (r + 1)),
      φ (zeta F (r + 1) a * g) * φ' (zeta F (r + 1) a * g) = ideleChar F χ a * (φ g * φ' g))
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : Continuous Φ) (s : ℂ)
    (hfin : ∫⁻ x, thetaKernelNorm F r (fun g => φ g * φ' g) Φ s (Quotient.out x)
      ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (r + 1)) < ⊤) :
    Integrable (equalIntegrand F χ φ φ' Φ s) (centralQuotientMeasure F (r + 1)) ∧
      equalIntegral F χ φ φ' Φ s = ∫ x, thetaKernel F r (fun g => φ g * φ' g) Φ s (Quotient.out x)
        ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (r + 1)) := by
  have hn : 0 < r + 1 := Nat.succ_pos r
  set P : Points F (r + 1) → ℂ := fun g => φ g * φ' g with hPdef
  have hPc : Continuous P := hφc.mul hφ'c
  have hPr : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      P (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = P g := fun c g => by
    simp only [hPdef, hφr, hφ'r]
  have hPz : ∀ (a : Points F 1) (g : Points F (r + 1)),
      P (zeta F (r + 1) a * g) = ideleChar F χ a * P g := hcent
  set f : Points F (r + 1) → ℂ := fun g => P g * eisensteinSeries F χ Φ s g with hfdef
  -- invariance of the integrand
  have hfr : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      f (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = f g := by
    intro c g
    have h1 : AdelicGroupPoints.rational F (Scheme F (r + 1)) c =
        rationalPoint F (r + 1) (GeneralLinearGroupPoints.rationalEquiv F (r + 1) c) := by
      simp only [rationalPoint, MulEquiv.symm_apply_apply]
    simp only [hfdef, hPr]
    rw [h1, eisensteinSeries_rational_mul]
  have hfz : ∀ (a : Points F 1) (g : Points F (r + 1)), f (zeta F (r + 1) a * g) = f g := by
    intro a g
    simp only [hfdef, hPz, eisensteinSeries_zeta_mul]
    have := ideleChar_ne_zero F χ a
    field_simp
  have hfinv := centralRationalSubgroup_invariant F f hfr hfz
  have hfm : StronglyMeasurable f :=
    hPc.stronglyMeasurable.mul (stronglyMeasurable_eisensteinSeries F r χ hΦ s)
  have hint_eq : equalIntegrand F χ φ φ' Φ s = fun q => f (Quotient.out q) := rfl
  -- the kernel on the quotient
  set Γ := glRational F (r + 1)
  have hKr := glRational_invariant F r (thetaKernel_rational_mul F r hPr Φ s)
  have hKnr := glRational_invariant F r (thetaKernelNorm_rational_mul F r hPr Φ s)
  have hK : (fun x : AdelicGroupPoints.RationalQuotient F (Scheme F (r + 1)) =>
      thetaKernel F r P Φ s (Quotient.out x)) = LeftCosetSpace.lift Γ _ hKr :=
    funext fun x => (UnequalAnalytic.lift_eq_out Γ _ hKr x).symm
  have hKn : (fun x : AdelicGroupPoints.RationalQuotient F (Scheme F (r + 1)) =>
      thetaKernelNorm F r P Φ s (Quotient.out x)) = LeftCosetSpace.lift Γ _ hKnr :=
    funext fun x => (UnequalAnalytic.lift_eq_out Γ _ hKnr x).symm
  have hKnm : Measurable (LeftCosetSpace.lift Γ _ hKnr) :=
    measurable_from_quotient.2 (measurable_thetaKernelNorm F r hPc hΦ s)
  have hKm' : Measurable (LeftCosetSpace.lift Γ _ hKr) :=
    measurable_from_quotient.2 (stronglyMeasurable_thetaKernel F r hPc hΦ s).measurable
  have hKm : StronglyMeasurable (LeftCosetSpace.lift Γ _ hKr) := hKm'.stronglyMeasurable
  rw [hKn] at hfin
  have hfin0 := hfin
  -- the fibred integral of the majorant
  have hfib := lintegral_rationalQuotient_eq F (r + 1) hn _ hKnm
  rw [hfib] at hfin
  set I : Points F (r + 1) → ℝ≥0∞ := fun g => ∫⁻ a in ideleDomain F,
    thetaKernelNorm F r P Φ s (zeta F (r + 1) a * g) ∂ideleMeasure F with hIdef
  -- pointwise bound for the integrand
  have hbound : ∀ g, ‖f g‖ₑ ≤ I g := by
    intro g
    rw [hfdef, enorm_mul, hIdef]
    simp only [thetaKernelNorm_zeta_mul F r hPz]
    rw [lintegral_const_mul' _ _ (by
      exact ENNReal.mul_ne_top enorm_ne_top enorm_ne_top), mul_assoc]
    gcongr
    exact enorm_eisensteinSeries_le F r χ hΦ s g
  -- integrability
  have hfint : IntegrableOn f (glDomain F (r + 1) ∩ glSlab F (r + 1)) Measure.haar :=
    ⟨hfm.aestronglyMeasurable, lt_of_le_of_lt (lintegral_mono fun g => hbound g) hfin⟩
  refine ⟨?_, ?_⟩
  · rw [hint_eq]
    exact (integrable_centralQuotientMeasure_iff F (r + 1) hfm hfinv).2 hfint
  -- the integral
  have hKint : Integrable (LeftCosetSpace.lift Γ _ hKr)
      (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (r + 1))) := by
    refine ⟨hKm.aestronglyMeasurable, lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin0⟩
    obtain ⟨g, rfl⟩ := LeftCosetSpace.mk_surjective Γ x
    exact enorm_thetaKernel_le F r P Φ s g
  have hIm : Measurable I := by
    have h1 : Measurable fun p : Points F (r + 1) × Points F 1 =>
        thetaKernelNorm F r P Φ s (zeta F (r + 1) p.2 * p.1) :=
      (measurable_thetaKernelNorm F r hPc hΦ s).comp
        (((continuous_zeta F (r + 1)).measurable.comp measurable_snd).mul measurable_fst)
    exact h1.lintegral_prod_right'
  have hae : ∀ᵐ g ∂(Measure.haar.restrict (glDomain F (r + 1) ∩ glSlab F (r + 1))), I g < ⊤ :=
    ae_lt_top hIm hfin.ne
  rw [equalIntegral, hint_eq, integral_centralQuotientMeasure F (r + 1) hfm hfinv, hK,
    integral_rationalQuotient_eq F (r + 1) hn hKm.aestronglyMeasurable hKint]
  refine integral_congr_ae ?_
  filter_upwards [hae] with g hg
  show f g = ∫ a in ideleDomain F, thetaKernel F r P Φ s (zeta F (r + 1) a * g) ∂ideleMeasure F
  simp only [thetaKernel_zeta_mul F r hPz]
  rw [integral_const_mul]
  by_cases hP0 : P g = 0
  · simp only [hfdef, hP0, zero_mul]
  · have hfin_g : ∫⁻ a in ideleDomain F, ‖sectionWeight (F := F) r χ s a‖ₑ *
        thetaNorm F (r + 1) Φ (E (r + 1) (zeta F (r + 1) a * g)) ∂ideleMeasure F ≠ ⊤ := by
      intro htop
      have hI : I g = ‖P g‖ₑ * ‖detPower F (r + 1) g s‖ₑ * ⊤ := by
        rw [hIdef]
        simp only [thetaKernelNorm_zeta_mul F r hPz]
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top), htop]
      have hd : ‖detPower F (r + 1) g s‖ₑ ≠ 0 := enorm_ne_zero.2 (Complex.exp_ne_zero _)
      rw [hI, ENNReal.mul_top (mul_ne_zero (enorm_ne_zero.2 hP0) hd)] at hg
      exact lt_irrefl _ hg
    rw [hfdef]
    simp only
    rw [eisensteinSeries_eq F r χ hΦ s g hfin_g]
    simp only [hPdef]
    ring

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
