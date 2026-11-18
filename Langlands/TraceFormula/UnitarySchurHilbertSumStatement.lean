import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Schur's lemma for unitary representations and irreducible subspaces of Hilbert sums (statement)

Let a group `M` act on a complex Hilbert space `E` by isometric bounded operators
`ρ : M →* (E →L[ℂ] E)` (a unitary representation; no continuity in `M` is assumed).

1. (Schur's lemma) If `E` has no closed invariant subspaces other than `⊥` and `⊤`, every bounded
   operator commuting with all `ρ a` is a scalar multiple of the identity.
2. If `E` is the Hilbert sum of a family `A` of irreducible closed invariant subspaces, then every
   nonzero irreducible closed invariant subspace `Q` of `E` is equivalent to some member `P` of
   `A` through an intertwining linear isometric equivalence `Q ≃ₗᵢ[ℂ] P`.

Together with the multiplicity-one statement for the cuspidal spectrum of `GL_n` in the Library
(`Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearCuspidalMultiplicityOneStatement`), the
second part shows that `Q` is itself a member of `A`. See the paired Markdown.
-/

universe u v

namespace Langlands.TraceFormula

/-- **Schur's lemma for unitary representations, and irreducible subspaces of Hilbert sums.**
For a group `M` acting on a complex Hilbert space `E` by isometric bounded operators `ρ a`:
(1) if `E` is topologically irreducible, the bounded operators commuting with every `ρ a` are the
scalars; (2) if `E` is the Hilbert sum of a family `A` of irreducible closed invariant subspaces,
every nonzero irreducible closed invariant subspace `Q` admits an intertwining linear isometric
equivalence onto some member of `A`. -/
def UnitarySchurHilbertSumStatement : Prop :=
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (M : Type v) [Group M] (ρ : M →* (E →L[ℂ] E)),
      (∀ a x, ‖ρ a x‖ = ‖x‖) →
      (∀ Q : Submodule ℂ E, IsClosed (Q : Set E) → (∀ a, ∀ x ∈ Q, ρ a x ∈ Q) →
        Q = ⊥ ∨ Q = ⊤) →
      ∀ B : E →L[ℂ] E, (∀ a, B ∘L ρ a = ρ a ∘L B) →
        ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ E) ∧
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (M : Type v) [Group M] (ρ : M →* (E →L[ℂ] E)),
      (∀ a x, ‖ρ a x‖ = ‖x‖) →
      ∀ (A : Set (Submodule ℂ E)) [∀ P : A, CompleteSpace (P : Submodule ℂ E)],
        (∀ P ∈ A, (∀ a, ∀ x ∈ P, ρ a x ∈ P) ∧
          ∀ P' : Submodule ℂ E, P' ≤ P → IsClosed (P' : Set E) →
            (∀ a, ∀ x ∈ P', ρ a x ∈ P') → P' = ⊥ ∨ P' = P) →
        IsHilbertSum ℂ (fun P : A => (P : Submodule ℂ E))
          (fun P => (P : Submodule ℂ E).subtypeₗᵢ) →
        ∀ Q : Submodule ℂ E, Q ≠ ⊥ → IsClosed (Q : Set E) →
          ∀ hQ : (∀ a, ∀ x ∈ Q, ρ a x ∈ Q),
            (∀ Q' : Submodule ℂ E, Q' ≤ Q → IsClosed (Q' : Set E) →
              (∀ a, ∀ x ∈ Q', ρ a x ∈ Q') → Q' = ⊥ ∨ Q' = Q) →
            ∃ P ∈ A, ∃ U : Q ≃ₗᵢ[ℂ] P,
              ∀ a (x : Q), (U ⟨ρ a x, hQ a x x.2⟩ : E) = ρ a (U x))

end Langlands.TraceFormula
