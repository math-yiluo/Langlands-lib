import Langlands.Global.LeftCosetFundamentalDomain
import Langlands.Analysis.Local.QuotientMeasureEquiv

/-! # Measure transport for discrete left quotients -/

noncomputable section

universe u v

open MeasureTheory Set

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

variable {H : Type u} {H' : Type v} [Group H] [Group H']
  [TopologicalSpace H] [TopologicalSpace H']
  [MeasurableSpace H] [MeasurableSpace H'] [BorelSpace H] [BorelSpace H']
  (e : H ≃ₜ* H') (Γ : Subgroup H) (Γ' : Subgroup H')
  (h : ∀ x, e x ∈ Γ' ↔ x ∈ Γ)

/-- The quotient equivalence induced by an isomorphism carrying one subgroup
onto the other. The measurable structures are the existing quotient structures. -/
def measurableEquivOfMulEquiv : LeftCosetSpace Γ ≃ᵐ LeftCosetSpace Γ' where
  toEquiv := (Homeomorph.Quotient.congr e.toHomeomorph (by
    intro x y
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change y * x⁻¹ ∈ Γ ↔ e y * (e x)⁻¹ ∈ Γ'
    rw [← map_inv, ← map_mul]
    exact (h _).symm)).toEquiv
  measurable_toFun := measurable_from_quotient.mpr ((measurable_mk Γ').comp e.continuous.measurable)
  measurable_invFun := measurable_from_quotient.mpr ((measurable_mk Γ).comp e.symm.continuous.measurable)

@[simp]
theorem measurableEquivOfMulEquiv_mk (x : H) :
    measurableEquivOfMulEquiv e Γ Γ' h (mk Γ x) = mk Γ' (e x) :=
  rfl

variable [IsTopologicalGroup H] [IsTopologicalGroup H']
  [SecondCountableTopology H] [SecondCountableTopology H']

/-- The pushforward of the fundamental-domain measure is the corresponding
fundamental-domain measure on the target quotient. -/
theorem measurePreserving_discreteQuotientMeasure (hΓ : IsDiscrete (Γ : Set H))
    (hΓ' : IsDiscrete (Γ' : Set H')) (μ : Measure H) (ν : Measure H') [ν.IsMulLeftInvariant]
    (he : MeasurePreserving e μ ν) :
    MeasurePreserving (measurableEquivOfMulEquiv e Γ Γ' h)
      (discreteQuotientMeasure Γ hΓ μ) (discreteQuotientMeasure Γ' hΓ' ν) := by
  let s := fundamentalDomain Γ hΓ
  let E := measurableEquivOfMulEquiv e Γ Γ' h
  let eΓ := Langlands.QuotientIntegration.subgroupContinuousMulEquiv e Γ Γ' h
  have hs : MeasurableSet s := measurableSet_fundamentalDomain Γ hΓ
  have hs' : MeasurableSet (e '' s) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.measurableSet_image' hs
  have huniq (y : H') : ∃! z : Γ', (z : H') * y ∈ e '' s := by
    have hiff (z : Γ) : (eΓ z : H') * y ∈ e '' s ↔ (z : H) * e.symm y ∈ s := by
      change e (z : H) * y ∈ e '' s ↔ (z : H) * e.symm y ∈ s
      rw [← e.apply_symm_apply y, ← map_mul, e.injective.mem_set_image, e.symm_apply_apply]
    obtain ⟨z, hz, hzuniq⟩ := fundamentalDomain_unique Γ hΓ (e.symm y)
    refine ⟨eΓ z, (hiff z).mpr hz, fun z' hz' => ?_⟩
    apply eΓ.symm.injective
    rw [eΓ.symm_apply_apply]
    apply hzuniq
    exact (hiff (eΓ.symm z')).mp (by simpa only [eΓ.apply_symm_apply] using hz')
  have hfund : IsFundamentalDomain Γ' (e '' s) ν :=
    IsFundamentalDomain.mk' hs'.nullMeasurableSet huniq
  refine ⟨E.measurable, ?_⟩
  ext T hT
  rw [Measure.map_apply E.measurable hT, discreteQuotientMeasure_eq Γ' hΓ' ν hfund]
  change quotientMeasure Γ μ s (E ⁻¹' T) = quotientMeasure Γ' ν (e '' s) T
  rw [quotientMeasure_apply Γ μ s (E.measurable hT),
    quotientMeasure_apply Γ' ν (e '' s) hT, ← he.map_eq]
  rw [Measure.map_apply he.measurable (((measurable_mk Γ') hT).inter hs')]
  congr 1
  ext x
  simp only [mem_preimage, mem_inter_iff, E, measurableEquivOfMulEquiv_mk, e.injective.mem_set_image]

end Langlands.Global.LeftCosetSpace

namespace Langlands.Global

open LeftCosetSpace

/-- The chosen measures of discrete left quotients are natural for a
measure-preserving ambient group isomorphism. -/
def DiscreteLeftCosetMeasureTransportStatement : Prop :=
  ∀ (H : Type u) (H' : Type v) [Group H] [Group H']
    [TopologicalSpace H] [TopologicalSpace H'] [IsTopologicalGroup H] [IsTopologicalGroup H']
    [MeasurableSpace H] [MeasurableSpace H'] [BorelSpace H] [BorelSpace H']
    [SecondCountableTopology H] [SecondCountableTopology H']
    (e : H ≃ₜ* H') (Γ : Subgroup H) (Γ' : Subgroup H') (h : ∀ x, e x ∈ Γ' ↔ x ∈ Γ)
    (hΓ : IsDiscrete (Γ : Set H)) (hΓ' : IsDiscrete (Γ' : Set H'))
    (μ : Measure H) (ν : Measure H') [ν.IsMulLeftInvariant],
    MeasurePreserving e μ ν →
      MeasurePreserving (measurableEquivOfMulEquiv e Γ Γ' h)
        (discreteQuotientMeasure Γ hΓ μ) (discreteQuotientMeasure Γ' hΓ' ν)

theorem discreteLeftCosetMeasureTransport : DiscreteLeftCosetMeasureTransportStatement.{u, v} := by
  intro H H' _ _ _ _ _ _ _ _ _ _ _ _ e Γ Γ' h hΓ hΓ' μ ν _ he
  exact measurePreserving_discreteQuotientMeasure e Γ Γ' h hΓ hΓ' μ ν he

end Langlands.Global
