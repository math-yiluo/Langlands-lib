import Langlands.Representation.Induction.Definitions
import Mathlib.Analysis.Complex.Basic

/-! # Failure of unnormalized induction to preserve Hermitian representations -/

namespace Langlands.Renard.CompactRepresentation

open Induction

/-- Renard IV.2.1, the paragraph after Remark 2. Even when `H` is closed and `H \ G`
is compact, unnormalized induction need not take a smooth Hermitian representation
of `H` to a Hermitian representation of `G`. -/
def UnnormalizedInductionHermitianCounterexampleStatement : Prop :=
  let IsHermitian {J : Type} [Group J] {V : Type} [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ J V) : Prop :=
    ∃ B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ,
      (∀ x y : V, B y x = starRingEnd ℂ (B x y)) ∧
      (∀ x : V, (∀ y : V, B x y = 0) → x = 0) ∧
      ∀ (g : J) (x y : V), B (ρ g x) (ρ g y) = B x y
  ¬ ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
      (H : Subgroup G), IsClosed (H : Set G) → CompactSpace (LeftQuotient H) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V),
        IsSmooth τ → IsHermitian τ → IsHermitian (compactInduced H τ)

end Langlands.Renard.CompactRepresentation
