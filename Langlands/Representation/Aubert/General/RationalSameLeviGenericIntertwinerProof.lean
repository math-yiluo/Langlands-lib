import Langlands.Representation.Aubert.General.RationalSameLeviGenericIntertwinerReduction
import Langlands.Representation.Aubert.General.RepresentedSameLeviGenericIntertwinerProof

/-! # Generic nonzero morphisms between inductions sharing a standard Levi -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- On a nonzero principal open locus of unramified characters of the standard
Levi `M_J(F)`, there is a nonzero morphism from the normalized induction along
`P_J` to the induction along the conjugate `g P_I g⁻¹`, which has the same Levi
subgroup `M_J(F)`. -/
theorem rationalSameLeviGenericNonzeroIntertwiner :
    RationalSameLeviGenericNonzeroIntertwinerStatement.{u, v} :=
  rationalSameLeviGenericNonzeroIntertwiner_of_represented
    RepresentedParabolic.representedSameLeviGenericNonzeroIntertwiner

end Langlands.Aubert.General.RationalPointFamily
