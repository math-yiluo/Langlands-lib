import Langlands.Representation.Hecke.CompactInductionModels

/-! # Normalized induction preserves Hermitian representations -/

noncomputable section

universe u v

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.2.1. Let `H` be a closed subgroup of a locally profinite group `G` with
compact `H \ G`. Normalized induction by the positive half of the relative modulus takes
every smooth representation with a nondegenerate invariant Hermitian form to one with such
a form. -/
def NormalizedInductionPreservesHermitianStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G] [T2Space G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ [LocallyCompactSpace H] [CompactSpace (Induction.LeftQuotient H)]
      (χ : Induction.SmoothCharacter ℂ H),
      let δ := Hecke.Homomorphism.relativeModularCharacter H.subtype continuous_subtype_val
      (∀ h : H, ∃ r : ℝ, 0 < r ∧ (χ.toMonoidHom h : ℂ) = r) →
      (∀ h : H, (χ.toMonoidHom h : ℂ) ^ 2 = (δ.toMonoidHom h : ℂ)) →
      ∀ (τ : SmoothRep.{0, u, v} ℂ H) (B : τ →ₗ⋆[ℂ] τ →ₗ[ℂ] ℂ),
        (∀ x y : τ, B y x = starRingEnd ℂ (B x y)) →
        (∀ x : τ, (∀ y, B x y = 0) → x = 0) →
        (∀ (h : H) (x y : τ), B (τ.representation h x) (τ.representation h y) = B x y) →
        let I := Induction.CompactFunctions H (twist χ.toMonoidHom τ.representation)
        let i := Induction.normalizedCompactInduced H χ τ.representation
        ∃ A : I →ₗ⋆[ℂ] I →ₗ[ℂ] ℂ,
          (∀ x y : I, A y x = starRingEnd ℂ (A x y)) ∧
          (∀ x : I, (∀ y, A x y = 0) → x = 0) ∧
          ∀ (g : G) (x y : I), A (i g x) (i g y) = A x y

end Langlands.Renard.CompactRepresentation
