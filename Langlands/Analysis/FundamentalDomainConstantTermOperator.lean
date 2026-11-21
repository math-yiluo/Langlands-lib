import Langlands.Analysis.FundamentalDomainConstantTermL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! # The constant term as a contraction of weighted `L²`

The folded constant term of `Langlands.Analysis.FundamentalDomainConstantTermL2` respects
equality almost everywhere for the weighted measure `W · μ|_D` and is additive almost
everywhere. It therefore defines a continuous linear operator of norm at most one on
`L²(W · μ|_D)`. -/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

open MeasureTheory Set Function
open scoped ENNReal

namespace Langlands.Analysis.FibreAverage

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
  {V : Type*} [Group V] [MeasurableSpace V] [MeasurableMul₂ V] [MeasurableInv V]
  (μ : Measure H) [μ.IsMulLeftInvariant] [SFinite μ]
  (Λ : Subgroup H) [Countable Λ] (D : Set H) (hDm : MeasurableSet D)
  (hD : ∀ x : H, ∃! l : Λ, (l : H) * x ∈ D)
  (j : V →* H) (hj : Measurable j) (hjinj : Injective j)
  (Γ : Subgroup V) (hΓ : ∀ v ∈ Γ, j v ∈ Λ)
  (cj : Λ → V → V) (hcj : ∀ l v, j (cj l v) = l * j v * (l : H)⁻¹)
  (hΓc : ∀ (l : Λ) (v : V), v ∈ Γ → cj l v ∈ Γ)
  (ν : Measure V) [ν.IsMulLeftInvariant] [ν.IsInvInvariant] [SFinite ν]
  (hcjm : ∀ l, MeasurePreserving (cj l) ν ν)
  (C : Set V) (hCm : MeasurableSet C) (hC : IsFundamentalDomain Γ C ν)
  (W : H → ℝ≥0∞) (hW : Measurable W) (hWΛ : ∀ l : Λ, ∀ x, W (l * x) = W x)
  (hWV : ∀ v x, W (j v * x) = W x)

include hDm hD hj hjinj hΓ hcj hΓc hcjm hCm hC hW hWΛ hWV in
/-- The fibre identity for squared norms: integrating the fibre integral of `‖f‖²` against
`W` over `D` gives `ν C` times the weighted norm of `f`. -/
theorem setLIntegral_fibre_sq_mul (f : H → ℂ) (hf : Measurable f) :
    ∫⁻ g in D, (∫⁻ v in C, ‖f (fold Λ hD (j v * g))‖ₑ ^ 2 ∂ν) * W g ∂μ =
      ν C * ∫⁻ g in D, ‖f g‖ₑ ^ 2 * W g ∂μ := by
  let F : H → ℝ≥0∞ := fun x => ‖f (fold Λ hD x)‖ₑ ^ 2 * W x
  have hF : Measurable F := ((hf.comp (measurable_fold Λ hD hDm)).enorm.pow_const 2).mul hW
  have hFΛ : ∀ l : Λ, ∀ x, F (l * x) = F x := by
    intro l x
    simp only [F, fold_mul_left, hWΛ]
  have hinner : ∀ g, (∫⁻ v in C, ‖f (fold Λ hD (j v * g))‖ₑ ^ 2 ∂ν) * W g =
      ∫⁻ v in C, F (j v * g) ∂ν := by
    intro g
    have hm : Measurable fun v : V => ‖f (fold Λ hD (j v * g))‖ₑ ^ 2 :=
      (hf.comp ((measurable_fold Λ hD hDm).comp (hj.mul_const g))).enorm.pow_const 2
    rw [← lintegral_mul_const _ hm]
    refine lintegral_congr fun v => ?_
    simp only [F, hWV]
  rw [lintegral_congr hinner,
    setLIntegral_fibreAverage μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC hF hFΛ]
  congr 1
  exact setLIntegral_congr_fun hDm fun g hg => by simp only [F, fold_of_mem Λ hD hg]

/-- The weighted measure `W · μ|_D`. -/
abbrev weightedMeasure : Measure H := (μ.restrict D).withDensity W

include hW in
theorem lintegral_weightedMeasure {φ : H → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ g, φ g ∂weightedMeasure μ D W = ∫⁻ g in D, φ g * W g ∂μ := by
  rw [weightedMeasure, lintegral_withDensity_eq_lintegral_mul _ hW hφ]
  exact lintegral_congr fun g => mul_comm _ _

include hDm hD hj hjinj hΓ hcj hΓc hcjm hCm hC hW hWΛ hWV in
/-- For a function with finite weighted norm, almost every fibre is integrable. -/
theorem ae_integrableOn_fibre (hCtop : ν C ≠ ∞) {f : H → ℂ} (hf : Measurable f)
    (hfin : ∫⁻ g in D, ‖f g‖ₑ ^ 2 * W g ∂μ ≠ ∞) :
    ∀ᵐ g ∂weightedMeasure μ D W, IntegrableOn (fun v => f (fold Λ hD (j v * g))) C ν := by
  have hm : Measurable fun g => ∫⁻ v in C, ‖f (fold Λ hD (j v * g))‖ₑ ^ 2 ∂ν :=
    Measurable.lintegral_prod_left
      (((hf.comp ((measurable_fold Λ hD hDm).comp
        ((hj.comp measurable_fst).mul measurable_snd))).enorm.pow_const 2))
  have hlt : ∫⁻ g, (∫⁻ v in C, ‖f (fold Λ hD (j v * g))‖ₑ ^ 2 ∂ν) ∂weightedMeasure μ D W
      ≠ ∞ := by
    rw [lintegral_weightedMeasure μ D W hW hm,
      setLIntegral_fibre_sq_mul μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW hWΛ
        hWV f hf]
    exact ENNReal.mul_ne_top hCtop hfin
  filter_upwards [ae_lt_top hm hlt] with g hg
  have : IsFiniteMeasure (ν.restrict C) := ⟨by simpa using hCtop.lt_top⟩
  have hlt2 : eLpNorm (fun v => f (fold Λ hD (j v * g))) 2 (ν.restrict C) < ∞ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    all_goals first
      | simpa [ENNReal.rpow_two] using hg
      | exact (hf.comp ((measurable_fold Λ hD hDm).comp (hj.mul_const g))).aestronglyMeasurable
  have hmem : MemLp (fun v => f (fold Λ hD (j v * g))) 2 (ν.restrict C) := hlt2
  exact hmem.integrable one_le_two

theorem foldConstantTerm_add {f f' : H → ℂ} {g : H}
    (hf : IntegrableOn (fun v => f (fold Λ hD (j v * g))) C ν)
    (hf' : IntegrableOn (fun v => f' (fold Λ hD (j v * g))) C ν) :
    foldConstantTerm Λ D hD j ν C (f + f') g =
      foldConstantTerm Λ D hD j ν C f g + foldConstantTerm Λ D hD j ν C f' g := by
  simp only [foldConstantTerm, Pi.add_apply]
  rw [integral_add hf hf', smul_add]

theorem foldConstantTerm_smul (c : ℂ) (f : H → ℂ) (g : H) :
    foldConstantTerm Λ D hD j ν C (c • f) g = c • foldConstantTerm Λ D hD j ν C f g := by
  simp only [foldConstantTerm, Pi.smul_apply]
  rw [integral_smul, smul_comm]

include hDm hj in
theorem stronglyMeasurable_foldConstantTerm {f : H → ℂ} (hf : Measurable f) :
    StronglyMeasurable (foldConstantTerm Λ D hD j ν C f) := by
  have hsm : StronglyMeasurable
      (uncurry fun (g : H) (v : V) => f (fold Λ hD (j v * g))) :=
    (hf.comp ((measurable_fold Λ hD hDm).comp
      ((hj.comp measurable_snd).mul measurable_fst))).stronglyMeasurable
  exact (StronglyMeasurable.integral_prod_right (ν := ν.restrict C) hsm).const_smul
    ((ν C).toReal)⁻¹

include hW in
theorem lintegral_enorm_sq_weightedMeasure {f : H → ℂ} (hf : Measurable f) :
    ∫⁻ g, ‖f g‖ₑ ^ (2 : ℝ≥0∞).toReal ∂weightedMeasure μ D W = ∫⁻ g in D, ‖f g‖ₑ ^ 2 * W g ∂μ := by
  rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num]
  simp_rw [ENNReal.rpow_two]
  exact lintegral_weightedMeasure μ D W hW (hf.enorm.pow_const 2)

include hDm hD hj hjinj hΓ hcj hΓc hcjm hCm hC hW hWΛ hWV in
/-- The folded constant term does not increase the norm of `L²(W · μ|_D)`. -/
theorem eLpNorm_foldConstantTerm_le (hC0 : ν C ≠ 0) (hCtop : ν C ≠ ∞) {f : H → ℂ}
    (hf : Measurable f) :
    eLpNorm (foldConstantTerm Λ D hD j ν C f) 2 (weightedMeasure μ D W) ≤
      eLpNorm f 2 (weightedMeasure μ D W) := by
  have hct := stronglyMeasurable_foldConstantTerm Λ D hDm hD j hj ν C hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hct.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable,
    lintegral_enorm_sq_weightedMeasure μ D W hW hct.measurable,
    lintegral_enorm_sq_weightedMeasure μ D W hW hf]
  exact ENNReal.rpow_le_rpow (setLIntegral_foldConstantTerm_le μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj
    hΓc ν hcjm C hCm hC hf hW hWΛ hWV hC0 hCtop) (by norm_num)

include hW in
theorem setLIntegral_ne_top_of_memLp {f : H → ℂ} (hf : Measurable f)
    (hfm : MemLp f 2 (weightedMeasure μ D W)) : ∫⁻ g in D, ‖f g‖ₑ ^ 2 * W g ∂μ ≠ ∞ := by
  have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    hf.aestronglyMeasurable).mp hfm
  rw [lintegral_enorm_sq_weightedMeasure μ D W hW hf] at h
  exact h.ne

include hDm hD hj hjinj hΓ hcj hΓc hcjm hCm hC hW hWΛ hWV in
theorem foldConstantTerm_ae_add (hCtop : ν C ≠ ∞) {f f' : H → ℂ} (hf : Measurable f)
    (hf' : Measurable f') (hfm : MemLp f 2 (weightedMeasure μ D W))
    (hfm' : MemLp f' 2 (weightedMeasure μ D W)) :
    foldConstantTerm Λ D hD j ν C (f + f') =ᵐ[weightedMeasure μ D W]
      foldConstantTerm Λ D hD j ν C f + foldConstantTerm Λ D hD j ν C f' := by
  filter_upwards [ae_integrableOn_fibre μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W
      hW hWΛ hWV hCtop hf (setLIntegral_ne_top_of_memLp μ D W hW hf hfm),
    ae_integrableOn_fibre μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W
      hW hWΛ hWV hCtop hf' (setLIntegral_ne_top_of_memLp μ D W hW hf' hfm')] with g h1 h2
  exact foldConstantTerm_add Λ D hD j ν C h1 h2

include hDm hD hj hjinj hΓ hcj hΓc hcjm hCm hC hW hWΛ hWV in
/-- The folded constant term respects equality almost everywhere for `W · μ|_D`. -/
theorem foldConstantTerm_ae_congr (hC0 : ν C ≠ 0) (hCtop : ν C ≠ ∞) {f f' : H → ℂ}
    (hf : Measurable f) (hf' : Measurable f') (hfm : MemLp f 2 (weightedMeasure μ D W))
    (hfm' : MemLp f' 2 (weightedMeasure μ D W)) (h : f =ᵐ[weightedMeasure μ D W] f') :
    foldConstantTerm Λ D hD j ν C f =ᵐ[weightedMeasure μ D W] foldConstantTerm Λ D hD j ν C f' := by
  have hd : Measurable (f - f') := hf.sub hf'
  have hdm : MemLp (f - f') 2 (weightedMeasure μ D W) := hfm.sub hfm'
  have hzero : eLpNorm (foldConstantTerm Λ D hD j ν C (f - f')) 2 (weightedMeasure μ D W) = 0 := by
    refine le_antisymm ?_ zero_le
    calc _ ≤ eLpNorm (f - f') 2 (weightedMeasure μ D W) :=
          eLpNorm_foldConstantTerm_le μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW
            hWΛ hWV hC0 hCtop hd
      _ = 0 := by
          rw [eLpNorm_eq_zero_iff two_ne_zero]
          filter_upwards [h] with g hg
          simp [hg]
  have hz := (eLpNorm_eq_zero_iff two_ne_zero).mp hzero
  have hadd := foldConstantTerm_ae_add μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW
    hWΛ hWV hCtop hd hf' hdm hfm'
  filter_upwards [hz, hadd] with g hg1 hg2
  simp only [sub_add_cancel, Pi.add_apply, Pi.zero_apply] at hg1 hg2
  rw [hg2, hg1, zero_add]

section Operator

/-- A strongly measurable representative of an `L²` class. -/
def rep (F : Lp ℂ 2 (weightedMeasure μ D W)) : H → ℂ := (Lp.aestronglyMeasurable F).mk F

theorem measurable_rep (F : Lp ℂ 2 (weightedMeasure μ D W)) : Measurable (rep μ D W F) :=
  (Lp.aestronglyMeasurable F).stronglyMeasurable_mk.measurable

theorem rep_ae (F : Lp ℂ 2 (weightedMeasure μ D W)) : rep μ D W F =ᵐ[weightedMeasure μ D W] F :=
  (Lp.aestronglyMeasurable F).ae_eq_mk.symm

theorem memLp_rep (F : Lp ℂ 2 (weightedMeasure μ D W)) : MemLp (rep μ D W F) 2 (weightedMeasure μ D W) :=
  (Lp.memLp F).ae_eq (rep_ae μ D W F).symm

variable (hC0 : ν C ≠ 0) (hCtop : ν C ≠ ∞)

include hDm hD hj hjinj hΓ hcj hΓc hcjm hCm hC hW hWΛ hWV hC0 hCtop in
theorem memLp_foldConstantTerm {f : H → ℂ} (hf : Measurable f)
    (hfm : MemLp f 2 (weightedMeasure μ D W)) :
    MemLp (foldConstantTerm Λ D hD j ν C f) 2 (weightedMeasure μ D W) :=
  (eLpNorm_foldConstantTerm_le μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW hWΛ hWV
    hC0 hCtop hf).trans_lt hfm

include hDm hD hj hjinj hΓ hcj hΓc hcjm hCm hC hW hWΛ hWV hC0 hCtop in
/-- The constant term of an `L²` class, computed on a measurable representative. -/
def foldConstantTermLp (F : Lp ℂ 2 (weightedMeasure μ D W)) : Lp ℂ 2 (weightedMeasure μ D W) :=
  (memLp_foldConstantTerm μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW hWΛ hWV
    hC0 hCtop (measurable_rep μ D W F) (memLp_rep μ D W F)).toLp _

theorem foldConstantTermLp_ae_of (F : Lp ℂ 2 (weightedMeasure μ D W)) {f : H → ℂ}
    (hf : Measurable f) (hfF : f =ᵐ[weightedMeasure μ D W] F) :
    foldConstantTermLp μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW hWΛ hWV
        hC0 hCtop F =ᵐ[weightedMeasure μ D W] foldConstantTerm Λ D hD j ν C f := by
  refine (MemLp.coeFn_toLp _).trans ?_
  exact foldConstantTerm_ae_congr μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW
    hWΛ hWV hC0 hCtop (measurable_rep μ D W F) hf (memLp_rep μ D W F)
    ((Lp.memLp F).ae_eq hfF.symm) ((rep_ae μ D W F).trans hfF.symm)

/-- **The constant term as a continuous linear operator of norm at most one on
`L²(W · μ|_D)`.** -/
def foldConstantTermCLM : Lp ℂ 2 (weightedMeasure μ D W) →L[ℂ] Lp ℂ 2 (weightedMeasure μ D W) :=
  LinearMap.mkContinuous
    { toFun := foldConstantTermLp μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW hWΛ
        hWV hC0 hCtop
      map_add' := fun F G => by
        apply Lp.ext
        have hsum : rep μ D W F + rep μ D W G =ᵐ[weightedMeasure μ D W] ⇑(F + G) := by
          filter_upwards [rep_ae μ D W F, rep_ae μ D W G, Lp.coeFn_add F G] with g h1 h2 h3
          rw [Pi.add_apply, h1, h2, h3, Pi.add_apply]
        filter_upwards [foldConstantTermLp_ae_of μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C
            hCm hC W hW hWΛ hWV hC0 hCtop (F + G) ((measurable_rep μ D W F).add
            (measurable_rep μ D W G)) hsum,
          foldConstantTerm_ae_add μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW hWΛ
            hWV hCtop (measurable_rep μ D W F) (measurable_rep μ D W G) (memLp_rep μ D W F)
            (memLp_rep μ D W G),
          Lp.coeFn_add (foldConstantTermLp μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC
            W hW hWΛ hWV hC0 hCtop F) (foldConstantTermLp μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc
            ν hcjm C hCm hC W hW hWΛ hWV hC0 hCtop G),
          MemLp.coeFn_toLp (memLp_foldConstantTerm μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C
            hCm hC W hW hWΛ hWV hC0 hCtop (measurable_rep μ D W F) (memLp_rep μ D W F)),
          MemLp.coeFn_toLp (memLp_foldConstantTerm μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C
            hCm hC W hW hWΛ hWV hC0 hCtop (measurable_rep μ D W G) (memLp_rep μ D W G))]
          with g h1 h2 h3 h4 h5
        rw [h1, h2, h3, Pi.add_apply, Pi.add_apply]
        simp only [foldConstantTermLp] at h4 h5 ⊢
        rw [h4, h5]
      map_smul' := fun c F => by
        apply Lp.ext
        have hsm : c • rep μ D W F =ᵐ[weightedMeasure μ D W] ⇑(c • F) := by
          filter_upwards [rep_ae μ D W F, Lp.coeFn_smul c F] with g h1 h2
          rw [Pi.smul_apply, h1, h2, Pi.smul_apply]
        filter_upwards [foldConstantTermLp_ae_of μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C
            hCm hC W hW hWΛ hWV hC0 hCtop (c • F) ((measurable_rep μ D W F).const_smul c) hsm,
          Lp.coeFn_smul c (foldConstantTermLp μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm
            hC W hW hWΛ hWV hC0 hCtop F),
          MemLp.coeFn_toLp (memLp_foldConstantTerm μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C
            hCm hC W hW hWΛ hWV hC0 hCtop (measurable_rep μ D W F) (memLp_rep μ D W F))]
          with g h1 h2 h3
        rw [h1, RingHom.id_apply, h2, Pi.smul_apply, foldConstantTerm_smul]
        simp only [foldConstantTermLp] at h3 ⊢
        rw [h3] }
    1 (fun F => by
      rw [one_mul, Lp.norm_def, Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top F) ?_
      calc eLpNorm (foldConstantTermLp μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W
            hW hWΛ hWV hC0 hCtop F) 2 (weightedMeasure μ D W)
          = eLpNorm (foldConstantTerm Λ D hD j ν C (rep μ D W F)) 2 (weightedMeasure μ D W) :=
            eLpNorm_congr_ae (MemLp.coeFn_toLp _)
        _ ≤ eLpNorm (rep μ D W F) 2 (weightedMeasure μ D W) :=
            eLpNorm_foldConstantTerm_le μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W
              hW hWΛ hWV hC0 hCtop (measurable_rep μ D W F)
        _ = eLpNorm F 2 (weightedMeasure μ D W) := eLpNorm_congr_ae (rep_ae μ D W F))

theorem foldConstantTermCLM_ae (F : Lp ℂ 2 (weightedMeasure μ D W)) {f : H → ℂ}
    (hf : Measurable f) (hfF : f =ᵐ[weightedMeasure μ D W] F) :
    foldConstantTermCLM μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW hWΛ hWV
        hC0 hCtop F =ᵐ[weightedMeasure μ D W] foldConstantTerm Λ D hD j ν C f :=
  foldConstantTermLp_ae_of μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW hWΛ hWV
    hC0 hCtop F hf hfF

theorem norm_foldConstantTermCLM_le :
    ‖foldConstantTermCLM μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW hWΛ hWV
      hC0 hCtop‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Operator

/-- **Statement form.** In the setting of `FundamentalDomainFibreAverageStatement`, with
`0 < ν C < ∞` and a measurable weight `W` invariant under `Λ` and under left multiplication by
`j V`, the folded constant term defines a continuous linear operator of norm at most one on
`L²((μ|_D).withDensity W)`, computed on every measurable representative. -/
def FoldConstantTermOperatorStatement : Prop :=
  ∀ {H : Type u} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
    {V : Type v} [Group V] [MeasurableSpace V] [MeasurableMul₂ V] [MeasurableInv V]
    (μ : Measure H) [μ.IsMulLeftInvariant] [SFinite μ]
    (Λ : Subgroup H) [Countable Λ] (D : Set H), MeasurableSet D →
    ∀ (hD : ∀ x : H, ∃! l : Λ, (l : H) * x ∈ D) (j : V →* H), Measurable j → Injective j →
    ∀ (Γ : Subgroup V), (∀ w ∈ Γ, j w ∈ Λ) →
    ∀ (cj : Λ → V → V), (∀ l w, j (cj l w) = l * j w * (l : H)⁻¹) →
    (∀ (l : Λ) (w : V), w ∈ Γ → cj l w ∈ Γ) →
    ∀ (ν : Measure V) [ν.IsMulLeftInvariant] [ν.IsInvInvariant] [SFinite ν],
    (∀ l, MeasurePreserving (cj l) ν ν) →
    ∀ (C : Set V), MeasurableSet C → IsFundamentalDomain Γ C ν → ν C ≠ 0 → ν C ≠ ∞ →
    ∀ (W : H → ℝ≥0∞), Measurable W → (∀ l : Λ, ∀ x, W (l * x) = W x) →
      (∀ w x, W (j w * x) = W x) →
    ∃ T : Lp ℂ 2 ((μ.restrict D).withDensity W) →L[ℂ] Lp ℂ 2 ((μ.restrict D).withDensity W),
      ‖T‖ ≤ 1 ∧ ∀ (F : Lp ℂ 2 ((μ.restrict D).withDensity W)) {f : H → ℂ}, Measurable f →
        f =ᵐ[(μ.restrict D).withDensity W] F →
        T F =ᵐ[(μ.restrict D).withDensity W] foldConstantTerm Λ D hD j ν C f

/-- Proof of `FoldConstantTermOperatorStatement`. -/
theorem foldConstantTermOperator : FoldConstantTermOperatorStatement.{u, v} := by
  intro H _ _ _ _ V _ _ _ _ μ _ _ Λ _ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν _ _ _ hcjm C hCm hC
    hC0 hCtop W hW hWΛ hWV
  exact ⟨foldConstantTermCLM μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW hWΛ hWV
      hC0 hCtop,
    norm_foldConstantTermCLM_le μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC W hW hWΛ
      hWV hC0 hCtop,
    fun F _ hf hfF => foldConstantTermCLM_ae μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC
      W hW hWΛ hWV hC0 hCtop F hf hfF⟩

end Langlands.Analysis.FibreAverage
