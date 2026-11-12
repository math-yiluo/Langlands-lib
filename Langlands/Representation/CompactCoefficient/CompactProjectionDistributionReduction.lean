import Langlands.Representation.CompactCoefficient.CompactProjectionDistributionConstruction
import Langlands.Representation.Smooth.RenardSchurStatements

/-! # Reduction of Renard IV.1.5 to completeness of irreducible Hecke actions -/

noncomputable section

universe u v w

open CategoryTheory MeasureTheory Langlands.HarmonicAnalysis

namespace Langlands.Renard.CompactRepresentation

namespace ProjectionDistribution

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]

/-- The defining action properties of a `(K, τ)`-projector. -/
def IsProjector (τ : SmoothRep.{0, u, v} ℂ G) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (e : Hecke.HeckeAlgebra μ) : Prop :=
  Hecke.heckeAction μ τ.representation τ.isSmooth e =
      Hecke.heckeAction μ τ.representation τ.isSmooth
        (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) ∧
    ∀ ρ : SmoothRep.{0, u, v} ℂ G, ρ.IsIrreducible → IsEmpty (ρ ≅ τ) →
      Hecke.heckeAction μ ρ.representation ρ.isSmooth e = 0

/-- Equality of two Hecke actions transports along an actual representation equivalence. -/
theorem action_eq_of_equiv {A : SmoothRep.{0, u, v} ℂ G}
    {B : SmoothRep.{0, u, w} ℂ G} (ε : A.representation.Equiv B.representation)
    {e f : Hecke.HeckeAlgebra μ}
    (h : Hecke.heckeAction μ B.representation B.isSmooth e =
      Hecke.heckeAction μ B.representation B.isSmooth f) :
    Hecke.heckeAction μ A.representation A.isSmooth e =
      Hecke.heckeAction μ A.representation A.isSmooth f := by
  ext a
  apply ε.injective
  change ε.toIntertwiningMap _ = ε.toIntertwiningMap _
  rw [Hecke.heckeAction_apply, Hecke.heckeAction_apply,
    Hecke.integratedAction_intertwiner μ A.isSmooth B.isSmooth ε.toIntertwiningMap,
    Hecke.integratedAction_intertwiner μ A.isSmooth B.isSmooth ε.toIntertwiningMap]
  exact congrArg (fun T : Module.End ℂ B => T (ε a)) h

section Conjugation

variable [μ.IsMulRightInvariant]

/-- Right translation moves the inverse group action onto the input vector. -/
theorem integratedAction_rightTranslate (A : SmoothRep.{0, u, w} ℂ G)
    (g : G) (f : SchwartzBruhat G) (a : A) :
    Hecke.integratedAction μ A.representation A.isSmooth
        (Hecke.TestFunction.rightTranslate g f) a =
      Hecke.integratedAction μ A.representation A.isSmooth f (A.representation g⁻¹ a) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro L
  rw [map_sub, sub_eq_zero, Hecke.integratedAction_dual, Hecke.integratedAction_dual]
  change (∫ x, f (x * g) * L (A.representation x a) ∂μ) = _
  rw [← integral_mul_right_eq_self (fun x => f (x * g) * L (A.representation x a)) g⁻¹]
  simp only [inv_mul_cancel_right, map_mul, Module.End.mul_apply]

/-- Conjugation of a Hecke function, with the conventions in the target statement. -/
def conjugate (g : G) (e : Hecke.HeckeAlgebra μ) : Hecke.HeckeAlgebra μ :=
  (Hecke.HeckeAlgebra.toTestFunction μ).symm
    (Hecke.TestFunction.rightTranslate g
      (Hecke.TestFunction.leftTranslate g (Hecke.HeckeAlgebra.toTestFunction μ e)))

/-- Conjugation of test functions becomes conjugation of their integrated operators. -/
theorem action_conjugate (A : SmoothRep.{0, u, w} ℂ G) (g : G)
    (e : Hecke.HeckeAlgebra μ) :
    Hecke.heckeAction μ A.representation A.isSmooth (conjugate μ g e) =
      A.representation g * Hecke.heckeAction μ A.representation A.isSmooth e *
        A.representation g⁻¹ := by
  ext a
  simp only [conjugate, Hecke.heckeAction_apply, LinearEquiv.apply_symm_apply,
    Module.End.mul_apply]
  rw [integratedAction_rightTranslate, Hecke.integratedAction_leftTranslate]

/-- Bi-invariance of Haar measure preserves the mass and normalized indicator of a conjugate. -/
theorem conjugate_normalizedIndicator (g : G) (K K' : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (hK' : IsCompact (K' : Set G))
    (hconj : ∀ x : G, x ∈ K' ↔ g⁻¹ * x * g ∈ K) :
    conjugate μ g (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) =
      Hecke.HeckeAlgebra.normalizedIndicator μ K' hK' := by
  classical
  have hset : (K' : Set G) =
      (fun x => x * g) ⁻¹' ((fun x => g⁻¹ * x) ⁻¹' (K : Set G)) := by
    ext x
    change (x ∈ K') ↔ g⁻¹ * (x * g) ∈ K
    simpa only [mul_assoc] using hconj x
  have hmass : μ.real (K' : Set G) = μ.real (K : Set G) := by
    unfold Measure.real
    rw [hset, measure_preimage_mul_right, measure_preimage_mul]
  ext x
  change Hecke.HeckeAlgebra.normalizedIndicator μ K hK (g⁻¹ * (x * g)) =
    Hecke.HeckeAlgebra.normalizedIndicator μ K' hK' x
  simp only [Hecke.HeckeAlgebra.normalizedIndicator_apply, hmass]
  congr 1
  change (if g⁻¹ * (x * g) ∈ K then (1 : ℂ) else 0) =
    if x ∈ K' then 1 else 0
  rw [← mul_assoc, ← hconj x]

/-- Conjugation preserves the defining projector property, without using completeness. -/
theorem isProjector_conjugate (τ : SmoothRep.{0, u, v} ℂ G)
    (g : G) (K K' : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (hK' : IsCompact (K' : Set G))
    (e : Hecke.HeckeAlgebra μ) (hconj : ∀ x : G, x ∈ K' ↔ g⁻¹ * x * g ∈ K)
    (he : IsProjector μ τ K hK e) :
    IsProjector μ τ K' hK' (conjugate μ g e) := by
  constructor
  · rw [action_conjugate, he.1, ← action_conjugate,
      conjugate_normalizedIndicator μ g K K' hK hK' hconj]
  · intro ρ hρ hn
    rw [action_conjugate, he.2 ρ hρ hn, mul_zero, zero_mul]

end Conjugation

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G]

/-- Completeness turns equality of all irreducible actions into equality in the Hecke algebra. -/
theorem eq_of_actions (hcomplete : Smooth.HeckeCompletenessStatement.{u, v})
    (e f : Hecke.HeckeAlgebra μ)
    (h : ∀ ρ : SmoothRep.{0, u, v} ℂ G, ρ.IsIrreducible →
      Hecke.heckeAction μ ρ.representation ρ.isSmooth e =
        Hecke.heckeAction μ ρ.representation ρ.isSmooth f) : e = f := by
  apply sub_eq_zero.mp
  by_contra hne
  obtain ⟨ρ, hρ, hn⟩ := hcomplete G μ (e - f) hne
  apply hn
  rw [map_sub, h ρ hρ, sub_self]

/-- It suffices to compare actions on `τ` and on inequivalent irreducibles. -/
theorem eq_of_tau_and_other_actions (hcomplete : Smooth.HeckeCompletenessStatement.{u, v})
    (τ : SmoothRep.{0, u, v} ℂ G) (e f : Hecke.HeckeAlgebra μ)
    (hτ : Hecke.heckeAction μ τ.representation τ.isSmooth e =
      Hecke.heckeAction μ τ.representation τ.isSmooth f)
    (hother : ∀ ρ : SmoothRep.{0, u, v} ℂ G, ρ.IsIrreducible → IsEmpty (ρ ≅ τ) →
      Hecke.heckeAction μ ρ.representation ρ.isSmooth e =
        Hecke.heckeAction μ ρ.representation ρ.isSmooth f) : e = f := by
  classical
  apply eq_of_actions μ hcomplete e f
  intro ρ hρ
  by_cases hi : Nonempty (ρ ≅ τ)
  · exact action_eq_of_equiv μ (SmoothRep.equivOfIso hi.some) hτ
  · exact hother ρ hρ ⟨fun ε => hi ⟨ε⟩⟩

/-- Uniqueness uses only the defining action conditions and completeness. -/
theorem unique (hcomplete : Smooth.HeckeCompletenessStatement.{u, v})
    (τ : SmoothRep.{0, u, v} ℂ G) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (e f : Hecke.HeckeAlgebra μ)
    (he : IsProjector μ τ K hK e) (hf : IsProjector μ τ K hK f) : e = f := by
  apply eq_of_tau_and_other_actions μ hcomplete τ e f (he.1.trans hf.1.symm)
  intro ρ hρ hn
  rw [he.2 ρ hρ hn, hf.2 ρ hρ hn]

/-- The three refinement identities follow by evaluating irreducible actions. -/
theorem refinement (hcomplete : Smooth.HeckeCompletenessStatement.{u, v})
    (τ : SmoothRep.{0, u, v} ℂ G) (K K' : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (hK' : IsCompact (K' : Set G))
    (e e' : Hecke.HeckeAlgebra μ) (hKK' : K' ≤ K)
    (he : IsProjector μ τ K hK e) (he' : IsProjector μ τ K' hK' e') :
    e' * e = e ∧ Hecke.HeckeAlgebra.normalizedIndicator μ K hK * e' = e ∧
      e' * Hecke.HeckeAlgebra.normalizedIndicator μ K hK = e := by
  refine ⟨?_, ?_, ?_⟩
  · apply eq_of_tau_and_other_actions μ hcomplete τ
    · rw [map_mul, he.1, he'.1, ← map_mul,
        Hecke.HeckeAlgebra.normalizedIndicator_mul_of_le μ K hK K' hK' hKK']
    · intro ρ hρ hn
      rw [map_mul, he.2 ρ hρ hn, mul_zero]
  · apply eq_of_tau_and_other_actions μ hcomplete τ
    · rw [map_mul, he.1, he'.1, ← map_mul,
        Hecke.HeckeAlgebra.normalizedIndicator_mul_of_ge μ K hK K' hK' hKK']
    · intro ρ hρ hn
      rw [map_mul, he'.2 ρ hρ hn, mul_zero, he.2 ρ hρ hn]
  · apply eq_of_tau_and_other_actions μ hcomplete τ
    · rw [map_mul, he.1, he'.1, ← map_mul,
        Hecke.HeckeAlgebra.normalizedIndicator_mul_of_le μ K hK K' hK' hKK']
    · intro ρ hρ hn
      rw [map_mul, he'.2 ρ hρ hn, zero_mul, he.2 ρ hρ hn]

end ProjectionDistribution

/-- Renard IV.1.5 reduces to completeness of irreducible Hecke actions. -/
theorem compactProjectionDistribution_of_heckeCompleteness
    (hcomplete : Smooth.HeckeCompletenessStatement.{u, v}) :
    CompactProjectionDistributionStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ _ μ _ _ _ τ hτ hc
  change (∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
      ∃! e, ProjectionDistribution.IsProjector μ τ K hK e) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨e, he⟩ := ProjectionDistribution.exists_element μ τ hτ hc K hK
    exact ⟨e, he, fun f hf => ProjectionDistribution.unique μ hcomplete τ K hK f e hf he⟩
  · intro K K' hK hK' e e' hKK' he he'
    exact ProjectionDistribution.refinement μ hcomplete τ K K' hK hK' e e' hKK' he he'
  · intro g K K' hK hK' e hconj he
    exact ProjectionDistribution.isProjector_conjugate μ τ g K K' hK hK' e hconj he

end Langlands.Renard.CompactRepresentation
