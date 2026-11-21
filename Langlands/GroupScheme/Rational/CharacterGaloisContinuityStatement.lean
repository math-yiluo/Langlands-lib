import Langlands.GroupScheme.Rational.CharacterGaloisAction
import Langlands.Representation.Smooth.Definitions
import Mathlib.FieldTheory.KrullTopology

/-! # Continuity of Galois transport on rational characters -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every character after an algebraic field extension is fixed by an open subgroup
of the Krull automorphism group, for a quasi-compact and quasi-separated group scheme. -/
def CharacterGaloisContinuityStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom],
    Langlands.IsSmooth (rationalCharacters.galoisRepresentation k K G)

end Langlands.GroupScheme
