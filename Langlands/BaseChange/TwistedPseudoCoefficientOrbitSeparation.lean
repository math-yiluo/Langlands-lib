import Langlands.BaseChange.TwistedInductionSpans
import Langlands.Representation.Twist.AlgebraProof

/-! # Localized separation of the twist orbit in the space of twisted distributions -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear

universe u v uG z uW

section Twists

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type z} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {θ : G ≃* G} {ρ : Representation ℂ G V} {π : Representation ℂ G W}

/-- The identity character puts `ρ` in its own unramified twist orbit. -/
theorem IsUnramifiedTwistOf.refl (θ : G ≃* G) (ρ : Representation ℂ G V) :
    IsUnramifiedTwistOf θ ρ ρ := by
  refine ⟨1, fun _ _ _ _ => rfl, fun _ => rfl, ?_⟩
  rw [twist_one]
  exact ⟨Representation.Equiv.refl ρ⟩

/-- The orbit is stable under further invariant unramified twists. -/
theorem IsUnramifiedTwistOf.twist (h : IsUnramifiedTwistOf θ ρ π)
    (ψ : G →* ℂˣ) (hψ : IsUnramifiedCharacter ψ) (hψθ : ∀ g, ψ (θ g) = ψ g) :
    IsUnramifiedTwistOf θ ρ (Langlands.twist ψ π) := by
  obtain ⟨η, hη, hηθ, ⟨e⟩⟩ := h
  refine ⟨ψ * η, ?_, ?_, ?_⟩
  · exact hψ.mul hη
  · intro g
    change ψ (θ g) * η (θ g) = ψ g * η g
    rw [hψθ, hηθ]
  · rw [← twist_twist ψ η]
    exact ⟨twistEquiv ψ e⟩

/-- Twisting by an invariant unramified character does not change membership in the orbit. -/
theorem isUnramifiedTwistOf_twist_iff (ψ : G →* ℂˣ) (hψ : IsUnramifiedCharacter ψ)
    (hψθ : ∀ g, ψ (θ g) = ψ g) :
    IsUnramifiedTwistOf θ ρ (twist ψ π) ↔ IsUnramifiedTwistOf θ ρ π := by
  refine ⟨fun h => ?_, fun h => h.twist ψ hψ hψθ⟩
  have hInvθ (g : G) : ψ⁻¹ (θ g) = ψ⁻¹ g := congrArg Inv.inv (hψθ g)
  have ht := h.twist ψ⁻¹ hψ.inv hInvθ
  rwa [twist_inv_twist] at ht

end Twists

section Subspaces

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  (θ : G ≃* G) {V : Type z} [AddCommGroup V] [Module ℂ V]
  (τ : Representation ℂ G V)

/-- The actual twisted-character span of the invariant unramified orbit of `τ`. -/
def twistedOrbitSpan : Submodule ℂ (Distribution G) :=
  twistedSpectrumSpan.{uG,z} μ θ (fun _ _ _ π => IsUnramifiedTwistOf θ τ π)

/-- The span of all twisted irreducible classes outside the orbit of `τ` whose
underlying representations become tempered after an invariant unramified twist. -/
def twistedOtherEssentiallyTemperedSpan : Submodule ℂ (Distribution G) :=
  twistedSpectrumSpan.{uG,z} μ θ (fun _ _ _ π => ¬ IsUnramifiedTwistOf θ τ π ∧
    ∃ ψ : G →* ℂˣ, IsUnramifiedCharacter ψ ∧ (∀ g, ψ (θ g) = ψ g) ∧
      IsTemperedRep (twist ψ π))

/-- The span of the irreducible twisted distributions without nonzero `J`-fixed vectors. -/
def twistedInvisibleSpan (J : OpenSubgroup G) : Submodule ℂ (Distribution G) :=
  twistedSpectrumSpan.{uG,z} μ θ (fun _ _ _ π => fixedVectors π J.toSubgroup = ⊥)

end Subspaces

section Complement

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {n : ℕ} (σ : E ≃ₐ[F] E)
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  (μ : Measure (GeneralLinear n E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  {W : Type z} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GeneralLinear n E) W)

/-- The sum of the twisted-character spans omitted by the orbit functional. -/
def twistedPseudoCoefficientComplementSpan (J : OpenSubgroup (GeneralLinear n E)) :
    Submodule ℂ (Distribution (GeneralLinear n E)) :=
  twistedOtherEssentiallyTemperedSpan μ (entrywiseAut σ n) τ ⊔
    sigmaProperInducedSpan.{u,v,z} σ μ ⊔ twistedInvisibleSpan.{v,z} μ (entrywiseAut σ n) J

end Complement

/-- For a σ-discrete series, its twist orbit is disjoint from the complementary span at
some compact open level. The two spaces span every irreducible twisted character. -/
def TwistedPseudoCoefficientSpectrumSplittingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) → 2 ≤ n →
    haveI : Module.Finite F E := hE.1
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ (W : Type z) [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W), IsSigmaDiscreteSeries σ n τ →
      ∀ (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure],
        let θ := entrywiseAut σ n
        ∃ J : OpenSubgroup (GeneralLinear n E), IsCompact (J : Set (GeneralLinear n E)) ∧
          let L := twistedOrbitSpan μ θ τ
          let N := twistedPseudoCoefficientComplementSpan σ μ τ J
          Disjoint L N ∧ twistedSpectrumSpan.{v,z} μ θ (fun _ _ _ _ => True) ≤ L ⊔ N

end Langlands.BaseChange
