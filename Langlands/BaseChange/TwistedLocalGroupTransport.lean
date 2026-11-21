import Langlands.BaseChange.OrbitalIntegral
import Langlands.BaseChange.TwistedCharacter.Basic
import Langlands.Representation.RankinSelberg.FieldTransport.Group
import Langlands.Representation.Character.TransportProof

/-! # Twisted orbital integrals and distribution characters through group isomorphisms -/

noncomputable section

set_option autoImplicit false

universe u v uV

namespace Langlands.BaseChange

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure QuotientIntegration TraceFormula

section Orbital

variable {G : Type u} {H : Type v} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  (e : G ≃ₜ* H) (θ : G →* G) (η : H →* H) (hθ : ∀ x, e (θ x) = η (e x)) (δ : G)

include hθ

/-- A compatible group isomorphism identifies the actual twisted centralizers. -/
theorem map_mem_twistedCentralizer_iff (x : G) :
    e x ∈ twistedCentralizer η (e δ) ↔ x ∈ twistedCentralizer θ δ := by
  rw [mem_twistedCentralizer, mem_twistedCentralizer, ← hθ x, ← map_inv, ← map_mul, ← map_mul,
    e.injective.eq_iff]

/-- Integration over the transported twisted centralizer quotient changes
variables by the group isomorphism. -/
theorem twistedOrbitalIntegral_map_equiv
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ δ))]
    [MeasurableSpace (LeftQuotient (twistedCentralizer η (e δ)))]
    [BorelSpace (LeftQuotient (twistedCentralizer η (e δ)))]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))) (f : H → ℂ) :
    twistedOrbitalIntegral η (e δ)
        (ν.map (cosetHomeomorph e (map_mem_twistedCentralizer_iff e θ η hθ δ))) f =
      twistedOrbitalIntegral θ δ ν (f ∘ e) := by
  let eq := cosetHomeomorph e (map_mem_twistedCentralizer_iff e θ η hθ δ)
  unfold twistedOrbitalIntegral
  rw [show ν.map eq = ν.map eq.toMeasurableEquiv from rfl, integral_map_equiv]
  congr 1
  funext q
  induction q using Quotient.inductionOn with
  | h x =>
    change f ((e x)⁻¹ * e δ * η (e x)) = f (e (x⁻¹ * δ * θ x))
    simp only [map_mul, map_inv, hθ x]

end Orbital

section Character

variable {G : Type u} {H : Type v} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [T2Space H] [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (e : G ≃ₜ* H) (μ : Measure G) [μ.IsHaarMeasure]
  (ρ : Representation ℂ H V) (hρ : IsAdmissible ρ) (heρ : IsAdmissible (ρ.comp e.toMonoidHom))

/-- The twisted distribution on the pulled-back representation equals the original
one on the transported test function and the pushed-forward Haar measure. -/
theorem twistedDistribution_comp_equiv (A : Module.End ℂ V) (f : SchwartzBruhat G) :
    letI := e.isHaarMeasure_map μ
    twistedDistribution μ (ρ.comp e.toMonoidHom) heρ A f =
      twistedDistribution (μ.map e) ρ hρ A (Hecke.TestFunction.pullback e.symm.toHomeomorph f) := by
  let := e.isHaarMeasure_map μ
  let f' := Hecke.TestFunction.pullback e.symm.toHomeomorph f
  have hp : MeasurePreserving e μ (μ.map e) := ⟨e.continuous.measurable, rfl⟩
  have hact : Hecke.integratedAction μ (ρ.comp e.toMonoidHom) heρ.1 f =
      Hecke.integratedAction (μ.map e) ρ hρ.1 f' := by
    ext v
    have heq : (Hecke.actionIntegrand ρ hρ.1 f' v).comp e hp.measurable =
        Hecke.actionIntegrand (ρ.comp e.toMonoidHom) heρ.1 f v := by
      ext x
      change f (e.symm (e x)) • ρ (e x) v = f x • ρ (e x) v
      rw [e.symm_apply_apply]
    have hi := AlgebraicIntegral.integral_comp_measurePreserving
      (Hecke.actionIntegrand ρ hρ.1 f' v) e hp
    rw [heq] at hi
    exact hi
  simp only [twistedDistribution_apply]
  apply congrArg FiniteRankEnd.trace
  apply Subtype.ext
  exact congrArg (fun T : Module.End ℂ V => T.comp A) hact

/-- The same change of variables applies to the ordinary distribution character. -/
theorem distribution_comp_equiv (f : SchwartzBruhat G) :
    letI := e.isHaarMeasure_map μ
    Character.distribution μ (ρ.comp e.toMonoidHom) heρ f =
      Character.distribution (μ.map e) ρ hρ (Hecke.TestFunction.pullback e.symm.toHomeomorph f) := by
  let := e.isHaarMeasure_map μ
  simpa only [twistedDistribution_one] using twistedDistribution_comp_equiv e μ ρ hρ heρ 1 f

end Character

/-- Twisted and ordinary character distributions are covariant under group
equivalence, using pushforward of the supplied Haar measure. -/
def TwistedDistributionEquivStatement : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H]
    [LocallyCompactSpace G] [LocallyCompactSpace H] [TotallyDisconnectedSpace G] [TotallyDisconnectedSpace H]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]
    (e : G ≃ₜ* H) (μ : Measure G) [μ.IsHaarMeasure]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (hρ : IsAdmissible ρ),
    ∃ heρ : IsAdmissible (ρ.comp e.toMonoidHom),
      letI := e.isHaarMeasure_map μ
      ∀ (A : Module.End ℂ V) (f : SchwartzBruhat G),
        twistedDistribution μ (ρ.comp e.toMonoidHom) heρ A f =
          twistedDistribution (μ.map e) ρ hρ A (Hecke.TestFunction.pullback e.symm.toHomeomorph f)

theorem twistedDistributionEquiv : TwistedDistributionEquivStatement.{u, v, uV} := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e μ _ V _ _ ρ hρ
  have heρ := isAdmissible_comp_continuousMulEquiv ρ e hρ
  exact ⟨heρ, twistedDistribution_comp_equiv e μ ρ hρ heρ⟩

end Langlands.BaseChange
