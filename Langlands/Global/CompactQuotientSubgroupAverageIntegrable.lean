import Langlands.Global.CompactQuotientSubgroupAverage
import Langlands.Global.LeftCosetMeasure

/-! # Integrable functions on a compact homogeneous quotient -/

noncomputable section

universe u v w

open MeasureTheory
open scoped CompactlySupported

namespace Langlands.Global.LeftCosetSpace

private theorem subgroupFiberEval_eq_apply {H N E : Type*} [Group H] [Group N]
    (Γ : Subgroup H) (Δ : Subgroup N) (j : N →* H) (hj : Δ ≤ Γ.comap j)
    (g : LeftCosetSpace Γ → E) (x : H) (q : LeftCosetSpace Δ) :
    subgroupFiberEval Γ Δ j hj g x q = g (subgroupFiberEval Γ Δ j hj id x q) := by
  obtain ⟨n, rfl⟩ := mk_surjective Δ q
  rfl

private theorem integral_eq_integral_mk {H E : Type*} [Group H] [MeasurableSpace H]
    (Γ : Subgroup H) (ρ : Measure H) {ν : Measure (LeftCosetSpace Γ)}
    (hρ : Measure.map (mk Γ) ρ = ν)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : LeftCosetSpace Γ → E} (hg : StronglyMeasurable g) :
    (∫ x, g x ∂ν) = ∫ x, g (mk Γ x) ∂ρ := by
  rw [← hρ, integral_map (measurable_mk Γ).aemeasurable hg.aestronglyMeasurable]

variable {H : Type u} {N : Type v} [Group H] [Group N]
  [TopologicalSpace H] [TopologicalSpace N] [IsTopologicalGroup H] [IsTopologicalGroup N]
  (Γ : Subgroup H) (Δ : Subgroup N) (j : N →* H) (hj : Δ ≤ Γ.comap j)
  (hjc : Continuous j)
  [MeasurableSpace (LeftCosetSpace Δ)] [BorelSpace (LeftCosetSpace Δ)]
  (μ : Measure (LeftCosetSpace Δ)) [IsProbabilityMeasure μ] [CompactSpace (LeftCosetSpace Δ)]
  (hconj : ∀ γ : Γ, ∃ e : LeftCosetSpace Δ ≃ₜ LeftCosetSpace Δ,
    MeasurePreserving e μ μ ∧ ∀ n : N,
      mk Γ (j n * γ) = subgroupFiberEval Γ Δ j hj id 1 (e (mk Δ n)))
  [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
  (hΓ : IsClosed (Γ : Set H)) [MeasurableSpace Γ] [BorelSpace Γ]
  (η : Measure Γ) [η.IsHaarMeasure] [η.Regular] [η.IsMulRightInvariant]
  [BorelSpace (LeftCosetSpace Γ)] [CompactSpace (LeftCosetSpace Γ)]
  (ν : Measure (LeftCosetSpace Γ)) [ν.Regular] [IsProbabilityMeasure ν]
  (hν : ∀ h : H, MeasurePreserving (rightTranslate Γ h) ν ν)
  (ρ : Measure H) [IsFiniteMeasure ρ] (hρ : Measure.map (mk Γ) ρ = ν)

include hjc hΓ η hν hρ in
/-- The compact subgroup average preserves integrals of measurable integrable functions
when the outer probability is presented as the pushforward of a finite measure. -/
theorem integral_compactSubgroupAverage_of_integrable
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : LeftCosetSpace Γ → E} (hfm : StronglyMeasurable f) (hfi : Integrable f ν) :
    (∫ q, compactSubgroupAverage Γ Δ j hj μ hconj f q ∂ν) = ∫ q, f q ∂ν := by
  let : IsClosed (Γ : Set H) := hΓ
  let b := fun p : H × LeftCosetSpace Δ => subgroupFiberEval Γ Δ j hj id p.1 p.2
  have hb : Measurable b := (continuous_subgroupFiberEval Γ Δ j hj hjc continuous_id).measurable
  have himage : Measure.map b (ρ.prod μ) = ν := by
    have : IsFiniteMeasure (Measure.map b (ρ.prod μ)) := Measure.isFiniteMeasure_map _ _
    have : (Measure.map b (ρ.prod μ)).Regular := inferInstance
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro g
    have hg : Integrable g (Measure.map b (ρ.prod μ)) :=
      g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
    rw [integral_map hb.aemeasurable hg.aestronglyMeasurable]
    have hgi : Integrable (fun p => g (b p)) (ρ.prod μ) :=
      (integrable_map_measure hg.aestronglyMeasurable hb.aemeasurable).mp hg
    rw [integral_prod _ hgi]
    let A := compactSubgroupAverage Γ Δ j hj μ hconj (fun q => g q)
    have hA : Continuous A := continuous_compactSubgroupAverage Γ Δ j hj hjc μ hconj g.continuous
    calc
      _ = ∫ x, A (mk Γ x) ∂ρ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change (∫ q, g (b (x, q)) ∂μ) =
          compactSubgroupAverage Γ Δ j hj μ hconj (fun q => g q) (mk Γ x)
        rw [compactSubgroupAverage_mk]
        exact integral_congr_ae (Filter.Eventually.of_forall fun q =>
          (subgroupFiberEval_eq_apply Γ Δ j hj (fun q => g q) x q).symm)
      _ = ∫ q, A q ∂ν := (integral_eq_integral_mk Γ ρ hρ hA.stronglyMeasurable).symm
      _ = _ :=
        integral_compactSubgroupAverage_real Γ Δ j hj hjc μ hconj hΓ η ν hν g.continuous
  have hbint : Integrable (f ∘ b) (ρ.prod μ) :=
    (integrable_map_measure hfm.aestronglyMeasurable hb.aemeasurable).mp (himage.symm ▸ hfi)
  have hA : StronglyMeasurable (compactSubgroupAverage Γ Δ j hj μ hconj f) := by
    apply Measurable.stronglyMeasurable
    apply measurable_from_quotient.mpr
    change Measurable (fun x : H => ∫ q, subgroupFiberEval Γ Δ j hj f x q ∂μ)
    simp_rw [subgroupFiberEval_eq_apply Γ Δ j hj f]
    exact (hfm.comp_measurable hb).integral_prod_right'.measurable
  calc
    (∫ q, compactSubgroupAverage Γ Δ j hj μ hconj f q ∂ν) =
        ∫ x, compactSubgroupAverage Γ Δ j hj μ hconj f (mk Γ x) ∂ρ :=
      integral_eq_integral_mk Γ ρ hρ hA
    _ = ∫ x, ∫ q, f (b (x, q)) ∂μ ∂ρ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change compactSubgroupAverage Γ Δ j hj μ hconj f (mk Γ x) = ∫ q, f (b (x, q)) ∂μ
      rw [compactSubgroupAverage_mk]
      exact integral_congr_ae (Filter.Eventually.of_forall fun q =>
        subgroupFiberEval_eq_apply Γ Δ j hj f x q)
    _ = ∫ p, f (b p) ∂(ρ.prod μ) := (integral_prod _ hbint).symm
    _ = ∫ q, f q ∂ν := by rw [← himage, integral_map hb.aemeasurable hfm.aestronglyMeasurable]

end Langlands.Global.LeftCosetSpace
