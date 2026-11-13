import Langlands.Representation.Aubert.General.RationalSameLeviGenericIrreducibilityStatement

/-! # Same-Levi generic isomorphism from generic irreducibility -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- If both normalized inductions in the same-Levi comparison are irreducible on one
nonzero principal open locus, then they are isomorphic on one nonzero principal open
locus. This is a proof target, not a theorem. -/
def RationalSameLeviGenericInductionIsoFromIrreducibilityStatement : Prop :=
  RationalSameLeviGenericInductionIrreducibilityStatement.{u, v} →
    RationalSameLeviGenericInductionIsoStatement.{u, v}

end Langlands.Aubert.General.RationalPointFamily
