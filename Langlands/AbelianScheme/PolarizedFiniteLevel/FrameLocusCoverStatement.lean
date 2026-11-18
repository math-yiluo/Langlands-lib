import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocus
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicProjectiveEvaluation

/-! # Covering by projective frame loci at large level -/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- For positive dimension and polarization index there is a bound `N` such that,
for every level `n ≥ N`, every point of every locally noetherian base on which
`n` is a unit lies in the projective frame locus of some family of
`6^g*d + 1` level coefficient tuples. This proposition is a statement, not a
proof of it. -/
def FrameLocusCoverStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (g d : ℕ), 0 < g → 0 < d →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (S : Scheme.{u}) [IsLocallyNoetherian S], IsUnit (n : Γ(S, ⊤)) →
        ∀ (a : Datum P S g d n) (x : S),
          ∃ ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n,
            x ∈ a.frameLocus ρ

end Langlands.AbelianScheme.PolarizedFiniteLevel
