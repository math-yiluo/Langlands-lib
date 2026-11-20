import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbedding

/-! # Uniqueness of frame-normalized cubic embeddings -/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry

/-- A datum whose projective frame locus for `ρ` is the whole base has at most one
frame-normalized cubic embedding for `ρ`: any two are equal as morphisms to relative
projective space. This proposition is a statement, not a proof of it. -/
def FrameEmbeddingUniquenessStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (S : Scheme.{u}) (g d n m : ℕ) (a : Datum P S g d n)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n)
    (ψ ψ' : a.abelian.X.left ⟶ RelativeProjectiveSpace S m),
    a.frameLocus ρ = ⊤ → a.IsFrameEmbedding ρ ψ → a.IsFrameEmbedding ρ ψ' → ψ = ψ'

end Langlands.AbelianScheme.PolarizedFiniteLevel
