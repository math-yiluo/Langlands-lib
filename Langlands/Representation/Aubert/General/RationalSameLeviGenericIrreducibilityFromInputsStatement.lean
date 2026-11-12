import Langlands.Representation.Aubert.General.RationalSameLeviGenericIrreducibilityStatement
import Langlands.Representation.Families.RenardGenericIrreducibilityStatements
import Langlands.Representation.Families.IrreducibleInducedTwistExistenceStatement

/-! # Same-Levi generic irreducibility from Renard VI.8.4 and one irreducible twist -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- If Renard VI.8.4 (an irreducible induced twist has a polynomial neighborhood of
irreducible induced twists) and the existence of one irreducible induced unramified
twist (Konno Theorem 4.2) hold, then both same-Levi inductions are irreducible on one
nonzero principal open locus. This is a proof target, not a theorem. -/
def RationalSameLeviGenericInductionIrreducibilityFromInputsStatement : Prop :=
  Renard.AlgebraicFamily.InducedIrreducibilityOpenStatement.{u, v} →
    Renard.AlgebraicFamily.IrreducibleInducedTwistExistenceStatement.{u, v} →
      RationalSameLeviGenericInductionIrreducibilityStatement.{u, v}

end Langlands.Aubert.General.RationalPointFamily
