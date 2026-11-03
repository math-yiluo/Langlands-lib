import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.FieldTheory.Perfect

/-! # Smooth connected unipotent groups over perfect fields are split -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected affine unipotent group over a perfect field admits a
finite normal series with actual represented fppf one-dimensional vector
quotients. This is the non-equivariant splitness assertion of Milne 16.24. -/
def PerfectFieldUnipotentSplitStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k]
    (U : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth U.X.hom] [IsAffineHom U.X.hom],
    ConnectedSpace U.X.left → IsUnipotent U → RelativeRoot.IsSplitUnipotent U

end Langlands.GroupScheme
