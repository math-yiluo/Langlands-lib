import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocus

/-! # The projective frame locus depends only on the isomorphism class of a datum -/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- Polarized-isomorphic ordinary polarized finite-level data over the same base have the
same projective frame locus for every family `ρ` of `m + 2` level coefficient tuples.
This proposition is a statement, not a proof of it. -/
def FrameLocusIsoInvarianceStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (S : Scheme.{u}) (g d n m : ℕ) (a b : Datum P S g d n)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n),
    Nonempty (PolarizedIso a b) → a.frameLocus ρ = b.frameLocus ρ

end Langlands.AbelianScheme.PolarizedFiniteLevel
