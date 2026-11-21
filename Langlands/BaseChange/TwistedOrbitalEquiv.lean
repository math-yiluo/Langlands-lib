import Langlands.Analysis.Local.QuotientMeasureEquiv
import Langlands.BaseChange.OrbitalIntegral

/-! # Twisted orbital integrals under a continuous group isomorphism -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.QuotientIntegration Langlands.TraceFormula

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

variable {G : Type u} {G' : Type v} [Group G] [Group G']
  [TopologicalSpace G] [TopologicalSpace G']
variable (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (he : ∀ x : G, e (θ x) = θ' (e x)) (δ : G)

include he in
private theorem mem_twistedCentralizer_map_iff (x : G) :
    e x ∈ twistedCentralizer θ' (e δ) ↔ x ∈ twistedCentralizer θ δ := by
  rw [mem_twistedCentralizer, mem_twistedCentralizer, ← he x,
    ← map_inv e, ← map_mul e, ← map_mul e, e.injective.eq_iff]

/-- Restrict an intertwining group isomorphism to the two twisted centralizers. -/
def twistedCentralizerEquiv :
    twistedCentralizer θ δ ≃ₜ* twistedCentralizer θ' (e δ) :=
  subgroupContinuousMulEquiv e _ _ (mem_twistedCentralizer_map_iff e θ θ' he δ)

@[simp] theorem twistedCentralizerEquiv_apply_coe (h : twistedCentralizer θ δ) :
    (twistedCentralizerEquiv e θ θ' he δ h : G') = e (h : G) := rfl

/-- Send the left coset represented by `x` to that represented by `e x`. -/
def twistedOrbitQuotientEquiv :
    LeftQuotient (twistedCentralizer θ δ) ≃ₜ LeftQuotient (twistedCentralizer θ' (e δ)) :=
  Homeomorph.Quotient.congr e.toHomeomorph (by
    intro a b
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change b * a⁻¹ ∈ twistedCentralizer θ δ ↔
      e b * (e a)⁻¹ ∈ twistedCentralizer θ' (e δ)
    rw [← map_inv e, ← map_mul e, mem_twistedCentralizer_map_iff e θ θ' he δ])

@[simp] theorem twistedOrbitQuotientEquiv_mk (x : G) :
    twistedOrbitQuotientEquiv e θ θ' he δ (Quotient.mk _ x) = Quotient.mk _ (e x) := rfl

/-- Simultaneous pushforward gives a compatible quotient measure for the
ambient and centralizer measures on the image group. -/
theorem isCompatible_map_twistedOrbit [IsTopologicalGroup G] [IsTopologicalGroup G']
    [MeasurableSpace G] [MeasurableSpace G'] [BorelSpace G] [BorelSpace G']
    (μ : Measure G)
    (μδ : Measure (twistedCentralizer θ δ)) [μδ.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ)))
    (hν : IsCompatible (twistedCentralizer θ δ) μ μδ ν) :
    let eH := twistedCentralizerEquiv e θ θ' he δ
    letI := isMulRightInvariant_map eH μδ
    IsCompatible (twistedCentralizer θ' (e δ)) (Measure.map e μ) (Measure.map eH μδ)
      (Measure.map (twistedOrbitQuotientEquiv e θ θ' he δ) ν) :=
  isCompatible_map_equiv e _ _ (twistedCentralizerEquiv e θ θ' he δ)
    (twistedCentralizerEquiv_apply_coe e θ θ' he δ)
    (twistedOrbitQuotientEquiv e θ θ' he δ)
    (twistedOrbitQuotientEquiv_mk e θ θ' he δ) μ μδ ν hν

/-- The change of variables preserves integrability and the total orbital integral. -/
theorem integrable_and_twistedOrbitalIntegral_map_equiv
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))) (f : G' → ℂ) :
    let ν' := Measure.map (twistedOrbitQuotientEquiv e θ θ' he δ) ν
    (Integrable (twistedOrbitFunction θ' (e δ) f) ν' ↔
      Integrable (twistedOrbitFunction θ δ (f ∘ e)) ν) ∧
    twistedOrbitalIntegral θ' (e δ) ν' f = twistedOrbitalIntegral θ δ ν (f ∘ e) := by
  let eQ := (twistedOrbitQuotientEquiv e θ θ' he δ).toMeasurableEquiv
  have hfun : twistedOrbitFunction θ' (e δ) f ∘ eQ =
      twistedOrbitFunction θ δ (f ∘ e) := by
    funext q
    induction q using Quotient.inductionOn with
    | h x =>
      change f ((e x)⁻¹ * e δ * θ' (e x)) = f (e (x⁻¹ * δ * θ x))
      rw [map_mul, map_mul, map_inv, he]
  constructor
  · change Integrable _ (Measure.map eQ ν) ↔ _
    rw [integrable_map_equiv, hfun]
  · change (∫ q, twistedOrbitFunction θ' (e δ) f q ∂Measure.map eQ ν) = _
    exact (integral_map_equiv eQ _).trans (congrArg (fun g => ∫ q, g q ∂ν) hfun)

/-- Under an intertwining continuous group isomorphism, compatibility and
orbital integrals are preserved with the corresponding pushforward measures. -/
def TwistedOrbitalEquivStatement : Prop :=
  ∀ {G : Type u} {G' : Type v} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G'] [IsTopologicalGroup G] [IsTopologicalGroup G']
    [MeasurableSpace G] [MeasurableSpace G'] [BorelSpace G] [BorelSpace G']
    (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
    (he : ∀ x : G, e (θ x) = θ' (e x)) (δ : G) (μ : Measure G)
    (μδ : Measure (twistedCentralizer θ δ)) [μδ.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))),
    IsCompatible (twistedCentralizer θ δ) μ μδ ν →
    let eH := twistedCentralizerEquiv e θ θ' he δ
    let ν' := Measure.map (twistedOrbitQuotientEquiv e θ θ' he δ) ν
    letI := isMulRightInvariant_map eH μδ
    IsCompatible (twistedCentralizer θ' (e δ)) (Measure.map e μ) (Measure.map eH μδ) ν' ∧
      ∀ f : G' → ℂ,
        (Integrable (twistedOrbitFunction θ' (e δ) f) ν' ↔
          Integrable (twistedOrbitFunction θ δ (f ∘ e)) ν) ∧
        twistedOrbitalIntegral θ' (e δ) ν' f = twistedOrbitalIntegral θ δ ν (f ∘ e)

theorem twistedOrbitalEquiv : TwistedOrbitalEquivStatement.{u, v} := by
  intro G G' _ _ _ _ _ _ _ _ _ _ e θ θ' he δ μ μδ _ ν hν
  exact ⟨isCompatible_map_twistedOrbit e θ θ' he δ μ μδ ν hν,
    integrable_and_twistedOrbitalIntegral_map_equiv e θ θ' he δ ν⟩

end Langlands.BaseChange
