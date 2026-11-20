import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbedding
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicProjectiveEvaluation

/-! # Existence of frame-normalized cubic embeddings -/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry

/-- Over a locally noetherian base, every datum with `0 < d` whose projective frame locus
for a family `ρ` of `6^g*d + 1` level coefficient tuples is the whole base has a
frame-normalized cubic embedding for `ρ` into relative projective
`cubicProjectiveDimension g d`-space. This proposition is a statement, not a proof of it. -/
def FrameEmbeddingExistenceStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (S : Scheme.{u}) [IsLocallyNoetherian S] (g d n : ℕ), 0 < d →
    ∀ (a : Datum P S g d n) (ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n),
      a.frameLocus ρ = ⊤ →
        ∃ ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S (cubicProjectiveDimension g d),
          a.IsFrameEmbedding ρ ψ

end Langlands.AbelianScheme.PolarizedFiniteLevel
