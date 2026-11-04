import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Perfect

/-! # One-dimensional unipotent groups over perfect fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected affine unipotent group of dimension one over a perfect
field is the one-dimensional vector group, with natural coordinates on all
relative scheme tests. This is the converse assertion of Milne 2017, 14.58. -/
def PerfectFieldOneDimensionalUnipotentStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k]
    (U : GroupScheme (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 U.X.hom] [IsAffineHom U.X.hom],
    ConnectedSpace U.X.left → IsUnipotent U →
      RelativeRoot.IsVectorGroupOfDimension U 1

end Langlands.GroupScheme
