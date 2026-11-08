import Langlands.Representation.Induction.CompactNormalizationTransport

/-! # Evaluation of normalized compact-induction transport -/

noncomputable section

universe u v w x

namespace Langlands.Induction.CompactNormalizationTransport

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  {W : Type w} [AddCommGroup W] [Module ℂ W]
  {X : Type x} [AddCommGroup X] [Module ℂ X]

/-- Normalized transport multiplies the postcomposed integral value by the
original ambient character at the unchanged argument. -/
theorem normalizedTransport_eval {H K : Subgroup G} (h : H = K)
    (ρ : Representation ℂ G X) (σ : Representation ℂ H V)
    (τ : Representation ℂ K W) (χ : SmoothCharacter ℂ G)
    (e0 : ρ.Equiv (compactInduced H σ))
    (e1 : Representation.Equiv
      ((Langlands.twist (χ.toMonoidHom.comp H.subtype) σ).comp
        (MulEquiv.subgroupCongr h).symm.toMonoidHom) τ)
    (a : X) (g : G) :
    eval K τ (normalizedTransport h ρ σ τ χ e0 e1 a).val g =
      (χ.toMonoidHom g : ℂ) • e1 (eval H σ (e0 a).val g) := by
  subst K
  change e1 ((χ.toMonoidHom g : ℂ) • eval H σ (e0 a).val g) = _
  exact e1.map_smul _ _

/-- Actual normalized values together with their evaluation identity and
their character-times-integral formula. -/
def normalizedTransportEvaluation {H K : Subgroup G} (h : H = K)
    (ρ : Representation ℂ G X) (σ : Representation ℂ H V)
    (τ : Representation ℂ K W) (χ : SmoothCharacter ℂ G)
    (e0 : ρ.Equiv (compactInduced H σ))
    (e1 : Representation.Equiv
      ((Langlands.twist (χ.toMonoidHom.comp H.subtype) σ).comp
        (MulEquiv.subgroupCongr h).symm.toMonoidHom) τ) :
    { f : X → G → W //
      (∀ a g, f a g = eval K τ (normalizedTransport h ρ σ τ χ e0 e1 a).val g) ∧
      (∀ a g, f a g = (χ.toMonoidHom g : ℂ) • e1 (eval H σ (e0 a).val g)) } :=
  ⟨fun a g => eval K τ (normalizedTransport h ρ σ τ χ e0 e1 a).val g,
    fun _ _ => rfl, normalizedTransport_eval h ρ σ τ χ e0 e1⟩

end Langlands.Induction.CompactNormalizationTransport
