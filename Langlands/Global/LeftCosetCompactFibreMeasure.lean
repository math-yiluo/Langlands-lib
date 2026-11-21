import Langlands.Global.LeftCosetClosedQuotientMeasure
import Langlands.Global.LeftCosetWeilMeasure
import Langlands.Analysis.Local.QuotientInvariantComparison
import Langlands.Analysis.Local.QuotientTopology

/-! # Pushforward from a discrete left quotient with compact fibres -/

noncomputable section

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace Langlands.Global.LeftCosetSpace

open Langlands.QuotientIntegration

universe u

section Projection

variable {G : Type u} [Group G] {Γ H : Subgroup G}

theorem projection_surjective (h : Γ ≤ H) : Function.Surjective (projectionOfLE h) := by
  intro q
  obtain ⟨g, rfl⟩ := mk_surjective H q
  exact ⟨mk Γ g, projectionOfLE_mk h g⟩

variable [TopologicalSpace G]

theorem continuous_projection (h : Γ ≤ H) : Continuous (projectionOfLE h) :=
  (continuous_iff Γ).mpr (continuous_mk H)

variable [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- A compact set of `H`-cosets has compact preimage among the `Γ`-cosets if
`Γ` is closed and its quotient in `H` is compact. -/
theorem isCompact_preimage_projection (h : Γ ≤ H) (hΓ : IsClosed (Γ : Set G))
    (hH : IsClosed (H : Set G)) [CompactSpace (LeftCosetSpace (Γ.subgroupOf H))]
    {C : Set (LeftCosetSpace H)} (hC : IsCompact C) : IsCompact (projectionOfLE h ⁻¹' C) := by
  have := leftQuotient_t2Space H hH
  have : LocallyCompactSpace H := hH.locallyCompactSpace
  obtain ⟨X, hX, hXC⟩ := leftQuotient_exists_isCompact_image H hH hC
  have hΓH : IsClosed (Γ.subgroupOf H : Set H) := hΓ.preimage continuous_subtype_val
  obtain ⟨Y, hY, hYall⟩ := leftQuotient_exists_isCompact_image (Γ.subgroupOf H) hΓH isCompact_univ
  let f (z : H × G) := mk Γ ((z.1 : G) * z.2)
  have hf : Continuous f :=
    (continuous_mk Γ).comp ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)
  apply ((hY.prod hX).image hf).of_isClosed_subset (hC.isClosed.preimage (continuous_projection h))
  intro z hz
  obtain ⟨g, rfl⟩ := mk_surjective Γ z
  have hg : mk H g ∈ leftQuotientMap H '' X := by
    rw [hXC]
    exact hz
  obtain ⟨x, hx, hxg⟩ := hg
  let t : H := ⟨g * x⁻¹, (mk_eq_mk_iff H x g).1 hxg⟩
  have ht : mk (Γ.subgroupOf H) t ∈ leftQuotientMap (Γ.subgroupOf H) '' Y := by
    rw [hYall]
    exact Set.mem_univ _
  obtain ⟨y, hy, hyt⟩ := ht
  refine ⟨(y, x), ⟨hy, hx⟩, (mk_eq_mk_iff Γ _ _).2 ?_⟩
  change g * ((y : G) * x)⁻¹ ∈ Γ
  rw [mul_inv_rev, ← mul_assoc]
  exact (mk_eq_mk_iff (Γ.subgroupOf H) y t).1 hyt

end Projection

/-- If a discrete subgroup has compact left quotient in a closed subgroup `H`,
then the discrete quotient measure projects to a positive finite multiple of
any compatible quotient measure on `H \ G`. -/
def DiscreteQuotientMeasurePushforwardStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G]
    (Γ H : Subgroup G) (h : Γ ≤ H) (hΓ : IsDiscrete (Γ : Set G))
    (_hH : IsClosed (H : Set G)) [CompactSpace (LeftCosetSpace (Γ.subgroupOf H))]
    (μ : Measure G) [IsHaarMeasure μ] [IsMulRightInvariant μ]
    (σ : Measure H) [IsHaarMeasure σ] [σ.Regular] [IsMulRightInvariant σ]
    (ν : Measure (LeftCosetSpace H)),
    IsCompatible H μ σ ν →
      ∃ c : ℝ, 0 < c ∧ Measure.map (projectionOfLE h) (discreteQuotientMeasure Γ hΓ μ) =
        ENNReal.ofReal c • ν

/-- Compact fibres ensure local finiteness of the pushforward. It is right invariant
and nonzero, so uniqueness of right-invariant regular measures gives the comparison. -/
theorem discreteQuotientMeasurePushforward : DiscreteQuotientMeasurePushforwardStatement.{u} := by
  intro G _ _ _ _ _ _ _ Γ H h hΓ hH _ μ _ _ σ _ _ _ ν hν
  have := leftQuotient_t2Space H hH
  have := leftQuotient_locallyCompactSpace H
  have := quotient_borelSpace H
  have := discreteQuotientBorelSpace Γ hΓ
  let μΓ := discreteQuotientMeasure Γ hΓ μ
  let ν' := Measure.map (projectionOfLE h) μΓ
  have hmeas : Measurable (projectionOfLE h) := (continuous_projection h).measurable
  have hμΓ : μΓ ≠ 0 := discreteQuotientMeasure_ne_zero Γ hΓ μ (NeZero.ne μ)
  have hν' : ν' ≠ 0 := by
    intro hzero
    apply hμΓ
    apply Measure.measure_univ_eq_zero.mp
    simpa only [ν', Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ,
      Measure.coe_zero, Pi.zero_apply] using
      congrArg (fun m : Measure (LeftCosetSpace H) => m Set.univ) hzero
  have := isLocallyFiniteMeasure_discreteQuotientMeasure Γ hΓ μ
  have : IsFiniteMeasureOnCompacts ν' := ⟨fun C hC => by
    rw [Measure.map_apply hmeas hC.isClosed.measurableSet]
    exact (isCompact_preimage_projection h (Γ.isClosed_of_isDiscrete hΓ) hH hC).measure_lt_top⟩
  have hright (g : G) : MeasurePreserving (QuotientIntegration.rightTranslate H g) ν' ν' := by
    have hg : Measurable (rightTranslate H g) := (continuous_rightTranslate H g).measurable
    have hgΓ := measurePreserving_rightTranslate_discrete Γ hΓ μ g
    have hcomm : rightTranslate H g ∘ projectionOfLE h = projectionOfLE h ∘ rightTranslate Γ g := by
      funext q
      obtain ⟨x, rfl⟩ := mk_surjective Γ q
      rfl
    refine ⟨hg, ?_⟩
    change Measure.map (rightTranslate H g) (Measure.map (projectionOfLE h) μΓ) = ν'
    rw [Measure.map_map hg hmeas, hcomm, ← Measure.map_map hmeas hgΓ.measurable, hgΓ.map_eq]
  have := hν.regular
  exact exists_pos_smul_eq_of_rightInvariant_quotient H hH σ ν' ν hν' hν.nonzero hright
    hν.right_invariant

end Langlands.Global.LeftCosetSpace
