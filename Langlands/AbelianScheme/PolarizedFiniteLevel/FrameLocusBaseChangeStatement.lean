import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocus
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicProjectiveEvaluation

/-! # Base change of the projective frame locus -/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- Over a locally noetherian base, the projective frame locus of a family of
`6^g*d + 1` level coefficient tuples is compatible with arbitrary base change:
the frame locus of the pulled-back datum is the preimage of the original frame
locus. This proposition is a statement, not a proof of it. -/
def FrameLocusBaseChangeStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (S T : Scheme.{u}) [IsLocallyNoetherian S] (g d n : ℕ),
    0 < d → ∀ (a : Datum P S g d n) (f : T ⟶ S)
      (ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n),
      (a.pullback f).frameLocus ρ = f ⁻¹ᵁ a.frameLocus ρ

end Langlands.AbelianScheme.PolarizedFiniteLevel
