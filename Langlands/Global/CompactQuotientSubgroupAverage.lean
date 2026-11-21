import Langlands.Analysis.Local.QuotientInvariantComparison
import Langlands.Analysis.Local.QuotientAutomorphismStatement
import Langlands.Global.LeftCosetSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Averaging along a compact subgroup quotient inside a compact homogeneous quotient

This is the measure argument used for transitivity of adelic unipotent constant terms.
The inner quotient is not a quotient *group*. We require that conjugation by the outer
lattice preserves the inner lattice and its probability measure, not that arbitrary
ambient points do so. -/

noncomputable section

open MeasureTheory Set Topology CompactlySupportedContinuousMap
open scoped CompactlySupported ENNReal

namespace Langlands.Global.LeftCosetSpace

universe u v w

section InvariantProbability

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (Γ : Subgroup H) (hΓ : IsClosed (Γ : Set H))
  [MeasurableSpace Γ] [BorelSpace Γ]
  (η : Measure Γ) [η.IsHaarMeasure] [η.Regular] [η.IsMulRightInvariant]
  [MeasurableSpace (LeftCosetSpace Γ)] [BorelSpace (LeftCosetSpace Γ)]

include hΓ η in
/-- A regular right-invariant probability measure on a left quotient is unique. -/
theorem eq_of_rightInvariant_probability
    (ν₁ ν₂ : Measure (LeftCosetSpace Γ)) [ν₁.Regular] [ν₂.Regular]
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : ∀ h : H, MeasurePreserving (rightTranslate Γ h) ν₁ ν₁)
    (h₂ : ∀ h : H, MeasurePreserving (rightTranslate Γ h) ν₂ ν₂) : ν₁ = ν₂ := by
  obtain ⟨c, -, he⟩ := QuotientIntegration.exists_pos_smul_eq_of_rightInvariant_quotient
    Γ hΓ η ν₁ ν₂ (NeZero.ne _) (NeZero.ne _) h₁ h₂
  have hone : ENNReal.ofReal c = 1 := by
    have h := congrArg (fun ν : Measure (LeftCosetSpace Γ) => ν univ) he
    simpa [Measure.smul_apply] using h.symm
  rw [he, hone, one_smul]

include hΓ η in
/-- A continuous automorphism preserving the lattice preserves a regular right-invariant
probability on its left quotient. -/
theorem measurePreserving_quotientAutomorphism_of_probability
    (ν : Measure (LeftCosetSpace Γ)) [ν.Regular] [IsProbabilityMeasure ν]
    (hν : ∀ h : H, MeasurePreserving (rightTranslate Γ h) ν ν)
    (a : H ≃ₜ* H) (ha : ∀ x : H, a x ∈ Γ ↔ x ∈ Γ) :
    MeasurePreserving (QuotientIntegration.quotientAutomorphism Γ a ha) ν ν := by
  let e := QuotientIntegration.quotientAutomorphism Γ a ha
  let ν' := Measure.map e ν
  have he : Measurable e := e.continuous.measurable
  have hm : MeasurePreserving e ν ν' := ⟨he, rfl⟩
  let : ν'.Regular := Measure.Regular.map e
  let : IsProbabilityMeasure ν' := ⟨by simp [ν', Measure.map_apply he MeasurableSet.univ]⟩
  refine ⟨he, eq_of_rightInvariant_probability Γ hΓ η ν' ν ?_ hν⟩
  intro h
  have hcomp : rightTranslate Γ h ∘ e = e ∘ rightTranslate Γ (a.symm h) := by
    funext q
    induction q using Quotient.inductionOn with
    | _ x =>
      change mk Γ (a x * h) = mk Γ (a (x * a.symm h))
      rw [map_mul, a.apply_symm_apply]
  have hl := (hν (a.symm h)).measurable
  refine ⟨(hν h).measurable, ?_⟩
  rw [← hm.map_eq, Measure.map_map (hν h).measurable he, hcomp,
    ← Measure.map_map he hl, (hν (a.symm h)).map_eq]

end InvariantProbability

section Average

variable {H : Type u} {N : Type v} [Group H] [Group N]
  [TopologicalSpace H] [TopologicalSpace N] [IsTopologicalGroup H]
  (Γ : Subgroup H) (Δ : Subgroup N) (j : N →* H) (hj : Δ ≤ Γ.comap j)

/-- The value of an outer quotient function at `[j(n) h]`, descended in `n`. -/
def subgroupFiberEval {E : Type w} (f : LeftCosetSpace Γ → E) (h : H) :
    LeftCosetSpace Δ → E :=
  lift Δ (fun n => f (mk Γ (j n * h))) (fun δ n => by
    rw [map_mul, mul_assoc]
    exact congrArg f (mk_subgroup_mul Γ ⟨j δ, hj δ.2⟩ (j n * h)))

omit [TopologicalSpace H] [TopologicalSpace N] [IsTopologicalGroup H] in
@[simp] theorem subgroupFiberEval_mk {E : Type w}
    (f : LeftCosetSpace Γ → E) (h : H) (n : N) :
    subgroupFiberEval Γ Δ j hj f h (mk Δ n) = f (mk Γ (j n * h)) := rfl

variable [IsTopologicalGroup N] (hjc : Continuous j)

include hjc in
/-- Joint continuity in the base representative and the inner quotient point. -/
theorem continuous_subgroupFiberEval {E : Type w} [TopologicalSpace E]
    {f : LeftCosetSpace Γ → E} (hf : Continuous f) :
    Continuous (fun p : H × LeftCosetSpace Δ => subgroupFiberEval Γ Δ j hj f p.1 p.2) := by
  rw [← (IsOpenQuotientMap.id.prodMap (isOpenQuotientMap_mk Δ)).continuous_comp_iff]
  exact hf.comp ((continuous_mk Γ).comp ((hjc.comp continuous_snd).mul continuous_fst))

variable [MeasurableSpace (LeftCosetSpace Δ)] [BorelSpace (LeftCosetSpace Δ)]
  (μ : Measure (LeftCosetSpace Δ))
  (hconj : ∀ γ : Γ, ∃ e : LeftCosetSpace Δ ≃ₜ LeftCosetSpace Δ,
    MeasurePreserving e μ μ ∧ ∀ n : N,
      mk Γ (j n * γ) = subgroupFiberEval Γ Δ j hj id 1 (e (mk Δ n)))

/-- The subgroup average on the outer quotient, when the fiber measure is preserved
under the change of representative. It is normalized if `μ` is a probability. -/
def compactSubgroupAverage {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : LeftCosetSpace Γ → E) : LeftCosetSpace Γ → E :=
  lift Γ (fun h => ∫ q, subgroupFiberEval Γ Δ j hj f h q ∂μ) (fun γ h => by
    obtain ⟨e, he, htransport⟩ := hconj γ
    have heq : subgroupFiberEval Γ Δ j hj f ((γ : H) * h) =
        subgroupFiberEval Γ Δ j hj f h ∘ e := by
      funext q
      induction q using Quotient.inductionOn with
      | _ n =>
        change f (mk Γ (j n * ((γ : H) * h))) = subgroupFiberEval Γ Δ j hj f h (e (mk Δ n))
        rw [← mul_assoc]
        have hq := congrArg (rightTranslate Γ h) (htransport n)
        rw [rightTranslate_mk] at hq
        rw [hq]
        generalize e (mk Δ n) = q'
        induction q' using Quotient.inductionOn with
        | _ n' =>
          change f (rightTranslate Γ h (mk Γ (j n' * 1))) = f (mk Γ (j n' * h))
          simp
    rw [heq]
    exact he.integral_comp e.measurableEmbedding _)

omit [TopologicalSpace H] [IsTopologicalGroup H] [IsTopologicalGroup N] in
@[simp] theorem compactSubgroupAverage_mk {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : LeftCosetSpace Γ → E) (h : H) :
    compactSubgroupAverage Γ Δ j hj μ hconj f (mk Γ h) =
      ∫ q, subgroupFiberEval Γ Δ j hj f h q ∂μ := rfl

include hjc in
/-- With compact fibers and a finite fiber measure the descended average is continuous. -/
theorem continuous_compactSubgroupAverage {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [CompactSpace (LeftCosetSpace Δ)] [IsFiniteMeasure μ]
    {f : LeftCosetSpace Γ → E} (hf : Continuous f) :
    Continuous (compactSubgroupAverage Γ Δ j hj μ hconj f) := by
  rw [continuous_iff Γ, ← continuousOn_univ]
  change ContinuousOn (fun h => ∫ q, subgroupFiberEval Γ Δ j hj f h q ∂μ) univ
  exact continuousOn_integral_of_compact_support (μ := μ) isCompact_univ
    (continuous_subgroupFiberEval Γ Δ j hj hjc hf).continuousOn (by simp)

omit [TopologicalSpace H] [IsTopologicalGroup H] [IsTopologicalGroup N] in
/-- Subgroup averaging commutes with right translation by the whole outer group. -/
theorem compactSubgroupAverage_rightTranslate {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : LeftCosetSpace Γ → E) (h : H) (q : LeftCosetSpace Γ) :
    compactSubgroupAverage Γ Δ j hj μ hconj (f ∘ rightTranslate Γ h) q =
      compactSubgroupAverage Γ Δ j hj μ hconj f (rightTranslate Γ h q) := by
  induction q using Quotient.inductionOn with
  | _ x =>
    change compactSubgroupAverage Γ Δ j hj μ hconj (f ∘ rightTranslate Γ h) (mk Γ x) =
      compactSubgroupAverage Γ Δ j hj μ hconj f (mk Γ (x * h))
    rw [compactSubgroupAverage_mk, compactSubgroupAverage_mk]
    congr 1
    funext r
    induction r using Quotient.inductionOn with
    | _ n => exact congrArg (fun z => f (mk Γ z)) (mul_assoc (j n) x h)

omit [TopologicalSpace H] [IsTopologicalGroup H] [IsTopologicalGroup N]
  [BorelSpace (LeftCosetSpace Δ)] in
/-- A map on the inner group conjugating by an outer lattice point and preserving the inner
lattice gives the representative comparison for `compactSubgroupAverage`. -/
theorem subgroupAverageConjugation
    (halpha : ∀ γ : Γ, ∃ a : N ≃ₜ* N, ∃ ha : ∀ n : N, a n ∈ Δ ↔ n ∈ Δ,
      MeasurePreserving (QuotientIntegration.quotientAutomorphism Δ a ha) μ μ ∧
      ∀ n : N, j (a n) = (γ : H)⁻¹ * j n * (γ : H)) :
    ∀ γ : Γ, ∃ e : LeftCosetSpace Δ ≃ₜ LeftCosetSpace Δ,
      MeasurePreserving e μ μ ∧ ∀ n : N,
        mk Γ (j n * γ) = subgroupFiberEval Γ Δ j hj id 1 (e (mk Δ n)) := by
  intro γ
  obtain ⟨a, ha, hmp, hmul⟩ := halpha γ
  refine ⟨QuotientIntegration.quotientAutomorphism Δ a ha, hmp, fun n => ?_⟩
  change mk Γ (j n * γ) = mk Γ (j (a n) * 1)
  rw [mul_one, ← mk_subgroup_mul Γ γ (j (a n)), hmul]
  simp only [← mul_assoc, mul_inv_cancel, one_mul]

include hjc in
private theorem integrable_subgroupFiberEval {E : Type w} [NormedAddCommGroup E]
    [CompactSpace (LeftCosetSpace Δ)] [IsFiniteMeasure μ]
    {f : LeftCosetSpace Γ → E} (hf : Continuous f) (h : H) :
    Integrable (subgroupFiberEval Γ Δ j hj f h) μ :=
  ((continuous_subgroupFiberEval Γ Δ j hj hjc hf).comp
    (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

section Compact

variable [CompactSpace (LeftCosetSpace Δ)] [IsProbabilityMeasure μ]
  [CompactSpace (LeftCosetSpace Γ)]

/-- Subgroup averaging is a positive linear map of real compact test functions. -/
def compactSubgroupAveragePositive : C_c(LeftCosetSpace Γ, ℝ) →ₚ[ℝ] C_c(LeftCosetSpace Γ, ℝ) :=
  PositiveLinearMap.mk₀
    { toFun f :=
        ⟨⟨compactSubgroupAverage Γ Δ j hj μ hconj f,
          continuous_compactSubgroupAverage Γ Δ j hj hjc μ hconj f.continuous⟩,
          HasCompactSupport.of_compactSpace _⟩
      map_add' f g := by
        ext q
        obtain ⟨x, rfl⟩ := mk_surjective Γ q
        change (∫ r, subgroupFiberEval Γ Δ j hj (↑(f + g)) x r ∂μ) =
          (∫ r, subgroupFiberEval Γ Δ j hj f x r ∂μ) +
            ∫ r, subgroupFiberEval Γ Δ j hj g x r ∂μ
        have hf : Continuous (f : LeftCosetSpace Γ → ℝ) := f.continuous
        have hg : Continuous (g : LeftCosetSpace Γ → ℝ) := g.continuous
        rw [← integral_add (integrable_subgroupFiberEval Γ Δ j hj hjc μ hf x)
          (integrable_subgroupFiberEval Γ Δ j hj hjc μ hg x)]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun r => by
          obtain ⟨n, rfl⟩ := mk_surjective Δ r
          rfl)
      map_smul' c f := by
        ext q
        obtain ⟨x, rfl⟩ := mk_surjective Γ q
        change (∫ r, subgroupFiberEval Γ Δ j hj (↑(c • f)) x r ∂μ) =
          c • ∫ r, subgroupFiberEval Γ Δ j hj f x r ∂μ
        rw [← integral_smul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun r => by
          obtain ⟨n, rfl⟩ := mk_surjective Δ r
          rfl) }
    (fun f hf q => by
      obtain ⟨x, rfl⟩ := mk_surjective Γ q
      change 0 ≤ ∫ r, subgroupFiberEval Γ Δ j hj f x r ∂μ
      exact integral_nonneg (fun r => by
        obtain ⟨n, rfl⟩ := mk_surjective Δ r
        exact hf (mk Γ (j n * x))))

variable [T2Space H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (hΓ : IsClosed (Γ : Set H)) [MeasurableSpace Γ] [BorelSpace Γ]
  (η : Measure Γ) [η.IsHaarMeasure] [η.Regular] [η.IsMulRightInvariant]
  [MeasurableSpace (LeftCosetSpace Γ)] [BorelSpace (LeftCosetSpace Γ)]
  (ν : Measure (LeftCosetSpace Γ)) [ν.Regular] [IsProbabilityMeasure ν]
  (hν : ∀ h : H, MeasurePreserving (rightTranslate Γ h) ν ν)

include hjc hΓ η hν in
/-- Averaging along an inner compact quotient preserves the outer invariant probability integral.
The proof compares regular probabilities using the positive linear map of subgroup averages. -/
theorem integral_compactSubgroupAverage_real {f : LeftCosetSpace Γ → ℝ}
    (hf : Continuous f) :
    (∫ q, compactSubgroupAverage Γ Δ j hj μ hconj f q ∂ν) = ∫ q, f q ∂ν := by
  let : IsClosed (Γ : Set H) := hΓ
  let A := compactSubgroupAveragePositive Γ Δ j hj hjc μ hconj
  let Λ := (integralPositiveLinearMap ν).comp A
  let σ := RealRMK.rieszMeasure Λ
  have hσ (g : C_c(LeftCosetSpace Γ, ℝ)) :
      (∫ q, g q ∂σ) = ∫ q, compactSubgroupAverage Γ Δ j hj μ hconj g q ∂ν :=
    RealRMK.integral_rieszMeasure Λ g
  let : IsProbabilityMeasure σ := ⟨by
    let o : C_c(LeftCosetSpace Γ, ℝ) := ⟨1, HasCompactSupport.of_compactSpace 1⟩
    have ho (q : LeftCosetSpace Γ) : compactSubgroupAverage Γ Δ j hj μ hconj o q = 1 := by
      obtain ⟨x, rfl⟩ := mk_surjective Γ q
      rw [compactSubgroupAverage_mk]
      have hfiber (r : LeftCosetSpace Δ) : subgroupFiberEval Γ Δ j hj o x r = 1 := by
        obtain ⟨n, rfl⟩ := mk_surjective Δ r
        rfl
      simp [hfiber]
    have h := hσ o
    simp_rw [ho] at h
    change (∫ _ : LeftCosetSpace Γ, (1 : ℝ) ∂σ) = ∫ _ : LeftCosetSpace Γ, (1 : ℝ) ∂ν at h
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_def, measure_univ,
      ENNReal.toReal_one] at h
    rw [← ENNReal.ofReal_toReal (measure_ne_top σ univ), h, ENNReal.ofReal_one]⟩
  have hinv (h : H) : MeasurePreserving (rightTranslate Γ h) σ σ := by
    let e := rightTranslateHomeomorph Γ h
    have : (Measure.map e σ).Regular := Measure.Regular.map e
    refine ⟨e.continuous.measurable, ?_⟩
    change Measure.map e σ = σ
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro g
    change (∫ q, g q ∂Measure.map e.toMeasurableEquiv σ) = _
    rw [integral_map_equiv e.toMeasurableEquiv (fun q => g q)]
    let gh : C_c(LeftCosetSpace Γ, ℝ) :=
      ⟨⟨g ∘ e, g.continuous.comp e.continuous⟩, HasCompactSupport.of_compactSpace _⟩
    change (∫ q, gh q ∂σ) = ∫ q, g q ∂σ
    rw [hσ, hσ]
    change (∫ q, compactSubgroupAverage Γ Δ j hj μ hconj (g ∘ rightTranslate Γ h) q ∂ν) = _
    simp_rw [compactSubgroupAverage_rightTranslate]
    exact (hν h).integral_comp e.measurableEmbedding _
  have heq := eq_of_rightInvariant_probability Γ hΓ η σ ν hinv hν
  let g : C_c(LeftCosetSpace Γ, ℝ) := ⟨⟨f, hf⟩, HasCompactSupport.of_compactSpace _⟩
  have h := hσ g
  rw [heq] at h
  exact h.symm

include hjc hΓ η hν in
/-- The compact subgroup averaging identity for real or complex valued continuous functions. -/
theorem integral_compactSubgroupAverage {𝕜 : Type w} [RCLike 𝕜]
    {f : LeftCosetSpace Γ → 𝕜} (hf : Continuous f) :
    (∫ q, compactSubgroupAverage Γ Δ j hj μ hconj f q ∂ν) = ∫ q, f q ∂ν := by
  let g := compactSubgroupAverage Γ Δ j hj μ hconj f
  have hg : Integrable g ν :=
    (continuous_compactSubgroupAverage Γ Δ j hj hjc μ hconj hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi : Integrable f ν := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply RCLike.ext
  · rw [← integral_re hg, ← integral_re hi]
    have havg (q : LeftCosetSpace Γ) : RCLike.re (g q) =
        compactSubgroupAverage Γ Δ j hj μ hconj (RCLike.re ∘ f) q := by
      obtain ⟨x, rfl⟩ := mk_surjective Γ q
      change RCLike.re (∫ r, subgroupFiberEval Γ Δ j hj f x r ∂μ) =
        ∫ r, subgroupFiberEval Γ Δ j hj (RCLike.re ∘ f) x r ∂μ
      rw [← integral_re (integrable_subgroupFiberEval Γ Δ j hj hjc μ hf x)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun r => by
        obtain ⟨n, rfl⟩ := mk_surjective Δ r
        rfl)
    simp_rw [havg]
    exact integral_compactSubgroupAverage_real Γ Δ j hj hjc μ hconj hΓ η ν hν
      (RCLike.continuous_re.comp hf)
  · rw [← integral_im hg, ← integral_im hi]
    have havg (q : LeftCosetSpace Γ) : RCLike.im (g q) =
        compactSubgroupAverage Γ Δ j hj μ hconj (RCLike.im ∘ f) q := by
      obtain ⟨x, rfl⟩ := mk_surjective Γ q
      change RCLike.im (∫ r, subgroupFiberEval Γ Δ j hj f x r ∂μ) =
        ∫ r, subgroupFiberEval Γ Δ j hj (RCLike.im ∘ f) x r ∂μ
      rw [← integral_im (integrable_subgroupFiberEval Γ Δ j hj hjc μ hf x)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun r => by
        obtain ⟨n, rfl⟩ := mk_surjective Δ r
        rfl)
    simp_rw [havg]
    exact integral_compactSubgroupAverage_real Γ Δ j hj hjc μ hconj hΓ η ν hν
      (RCLike.continuous_im.comp hf)

end Compact

end Average

end Langlands.Global.LeftCosetSpace
