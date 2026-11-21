import Langlands.Analysis.FundamentalDomainFibreAverage
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Fibre averages are contractions of weighted `L²` norms

With the data of `Langlands.Analysis.FundamentalDomainFibreAverage`, fold every point of `H`
into the strict fundamental domain `D` of `Λ`, and average a function over `C` after folding.
For a weight that is invariant under `Λ` and under left multiplication by `j V`, this
average does not increase the weighted `L²` norm over `D`. -/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

open MeasureTheory Set Function
open scoped ENNReal

namespace Langlands.Analysis.FibreAverage

section Fold

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
  (Λ : Subgroup H) {D : Set H} (hD : ∀ x : H, ∃! l : Λ, (l : H) * x ∈ D)

/-- The element of `Λ` that moves `x` into `D`. -/
def foldElement (x : H) : Λ := (hD x).choose

/-- The representative of the `Λ`-orbit of `x` in `D`. -/
def fold (x : H) : H := (foldElement Λ hD x : H) * x

theorem fold_mem (x : H) : fold Λ hD x ∈ D := (hD x).choose_spec.1

theorem foldElement_unique {x : H} {l : Λ} (hl : (l : H) * x ∈ D) : foldElement Λ hD x = l :=
  ((hD x).choose_spec.2 l hl).symm

theorem fold_mul_left (l : Λ) (x : H) : fold Λ hD ((l : H) * x) = fold Λ hD x := by
  have h : ((foldElement Λ hD ((l : H) * x) * l : Λ) : H) * x ∈ D := by
    have := fold_mem Λ hD ((l : H) * x)
    simpa [fold, mul_assoc] using this
  have := foldElement_unique Λ hD h
  simp only [fold]
  rw [this, Subgroup.coe_mul, mul_assoc]

theorem fold_of_mem {x : H} (hx : x ∈ D) : fold Λ hD x = x := by
  have : foldElement Λ hD x = 1 := foldElement_unique Λ hD (by simpa using hx)
  simp [fold, this]

theorem fold_preimage [Countable Λ] (A : Set H) :
    fold Λ hD ⁻¹' A = ⋃ l : Λ, (fun x => (l : H) * x) ⁻¹' (D ∩ A) := by
  ext x
  simp only [mem_preimage, mem_iUnion, mem_inter_iff]
  constructor
  · intro hx
    exact ⟨foldElement Λ hD x, fold_mem Λ hD x, hx⟩
  · rintro ⟨l, hlD, hlA⟩
    have := foldElement_unique Λ hD hlD
    simpa [fold, this] using hlA

theorem measurable_fold [Countable Λ] (hDm : MeasurableSet D) : Measurable (fold Λ hD) := by
  intro A hA
  rw [fold_preimage Λ hD A]
  exact MeasurableSet.iUnion fun l => (measurable_const_mul (l : H)) (hDm.inter hA)

end Fold

section Jensen

variable {α : Type*} [MeasurableSpace α]

/-- Jensen's inequality for the square on a probability measure, for `[0, ∞]`-valued
functions. -/
theorem sq_lintegral_le_lintegral_sq (P : Measure α) [IsProbabilityMeasure P] {a : α → ℝ≥0∞}
    (ha : AEMeasurable a P) : (∫⁻ x, a x ∂P) ^ 2 ≤ ∫⁻ x, a x ^ 2 ∂P := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two ha
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  calc (∫⁻ x, a x ∂P) ^ 2 ≤ ((∫⁻ x, a x ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le h 2
    _ = ∫⁻ x, a x ^ 2 ∂P := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

end Jensen

section ConstantTerm

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

/-- The constant term of `f` along `j V`: fold the translates `j v * g` into `D` and average
over the fundamental domain `C`, normalized to mass one. -/
def foldConstantTerm (f : H → ℂ) (g : H) : ℂ :=
  ((ν C).toReal)⁻¹ • ∫ v in C, f (fold Λ hD (j v * g)) ∂ν

include hCm in
/-- Pointwise Jensen bound for the folded constant term. -/
theorem enorm_foldConstantTerm_sq_le {f : H → ℂ} (hf : Measurable f) (hDm : MeasurableSet D)
    (hj : Measurable j) (hC0 : ν C ≠ 0) (hCtop : ν C ≠ ∞) (g : H) :
    ‖foldConstantTerm Λ D hD j ν C f g‖ₑ ^ 2 ≤
      (ν C)⁻¹ * ∫⁻ v in C, ‖f (fold Λ hD (j v * g))‖ₑ ^ 2 ∂ν := by
  let P : Measure V := (ν C)⁻¹ • ν.restrict C
  have hP : IsProbabilityMeasure P := by
    constructor
    simp only [P, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel hC0 hCtop
  let a : V → ℝ≥0∞ := fun v => ‖f (fold Λ hD (j v * g))‖ₑ
  have ha : Measurable a :=
    (hf.comp ((measurable_fold Λ hD hDm).comp (hj.mul_const g))).enorm
  have h1 : ‖foldConstantTerm Λ D hD j ν C f g‖ₑ ≤ ∫⁻ v, a v ∂P := by
    rw [foldConstantTerm, enorm_smul, lintegral_smul_measure, smul_eq_mul]
    have hc : ‖((ν C).toReal)⁻¹‖ₑ = (ν C)⁻¹ := by
      rw [Real.enorm_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg),
        ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hC0 hCtop), ENNReal.ofReal_toReal hCtop]
    rw [hc]
    exact mul_le_mul_right (enorm_integral_le_lintegral_enorm _) _
  calc ‖foldConstantTerm Λ D hD j ν C f g‖ₑ ^ 2 ≤ (∫⁻ v, a v ∂P) ^ 2 :=
        pow_le_pow_left₀ zero_le h1 2
    _ ≤ ∫⁻ v, a v ^ 2 ∂P := sq_lintegral_le_lintegral_sq P ha.aemeasurable
    _ = (ν C)⁻¹ * ∫⁻ v in C, ‖f (fold Λ hD (j v * g))‖ₑ ^ 2 ∂ν := by
        rw [lintegral_smul_measure, smul_eq_mul]

include hDm hD hj hjinj hΓ hcj hΓc hcjm hCm hC in
/-- **The folded constant term is a contraction of weighted `L²` norms over `D`**, for a weight
invariant under `Λ` and under left multiplication by `j V`. -/
theorem setLIntegral_foldConstantTerm_le {f : H → ℂ} (hf : Measurable f) {W : H → ℝ≥0∞}
    (hW : Measurable W) (hWΛ : ∀ l : Λ, ∀ x, W (l * x) = W x) (hWV : ∀ v x, W (j v * x) = W x)
    (hC0 : ν C ≠ 0) (hCtop : ν C ≠ ∞) :
    ∫⁻ g in D, ‖foldConstantTerm Λ D hD j ν C f g‖ₑ ^ 2 * W g ∂μ ≤
      ∫⁻ g in D, ‖f g‖ₑ ^ 2 * W g ∂μ := by
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
  have hfib := setLIntegral_fibreAverage μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC
    hF hFΛ
  calc ∫⁻ g in D, ‖foldConstantTerm Λ D hD j ν C f g‖ₑ ^ 2 * W g ∂μ
      ≤ ∫⁻ g in D, ((ν C)⁻¹ * ∫⁻ v in C, ‖f (fold Λ hD (j v * g))‖ₑ ^ 2 ∂ν) * W g ∂μ :=
        lintegral_mono fun g => mul_le_mul'
          (enorm_foldConstantTerm_sq_le Λ D hD j ν C hCm hf hDm hj hC0 hCtop g) le_rfl
    _ = (ν C)⁻¹ * ∫⁻ g in D, ∫⁻ v in C, F (j v * g) ∂ν ∂μ := by
        rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hC0)]
        refine lintegral_congr fun g => ?_
        rw [mul_assoc, hinner]
    _ = ∫⁻ g in D, F g ∂μ := by
        rw [hfib, ← mul_assoc, ENNReal.inv_mul_cancel hC0 hCtop, one_mul]
    _ = ∫⁻ g in D, ‖f g‖ₑ ^ 2 * W g ∂μ :=
        setLIntegral_congr_fun hDm fun g hg => by simp only [F, fold_of_mem Λ hD hg]

end ConstantTerm

/-- **Statement form.** In the setting of `FundamentalDomainFibreAverageStatement`, with
`ν C` finite and nonzero, the folded constant term does not increase the `L²` norm over `D`
weighted by any measurable `W ≥ 0` that is invariant under `Λ` and under left
multiplication by `j V`. -/
def FoldConstantTermContractionStatement : Prop :=
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
    ∀ {f : H → ℂ}, Measurable f → ∀ {W : H → ℝ≥0∞}, Measurable W →
      (∀ l : Λ, ∀ x, W (l * x) = W x) → (∀ w x, W (j w * x) = W x) →
      ∫⁻ g in D, ‖foldConstantTerm Λ D hD j ν C f g‖ₑ ^ 2 * W g ∂μ ≤
        ∫⁻ g in D, ‖f g‖ₑ ^ 2 * W g ∂μ

/-- Proof of `FoldConstantTermContractionStatement`. -/
theorem foldConstantTermContraction : FoldConstantTermContractionStatement.{u, v} := by
  intro H _ _ _ _ V _ _ _ _ μ _ _ Λ _ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν _ _ _ hcjm C hCm hC
    hC0 hCtop f hf W hW hWΛ hWV
  exact setLIntegral_foldConstantTerm_le μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC
    hf hW hWΛ hWV hC0 hCtop

end Langlands.Analysis.FibreAverage
