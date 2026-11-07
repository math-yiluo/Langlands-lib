import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointStatement

/-!
# Complete valued fields are henselian

Conrad restricts attention to complete ground fields (printed p.14): "The complete case is
all we will actually need". This presupposes that complete valued fields are henselian valued
fields, that is, that the absolute value of a complete field extends uniquely to every
algebraic extension.
-/

universe u

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Conrad, printed p.14: every complete nontrivially normed field is a henselian valued field.
Its absolute value extends uniquely to every algebraic extension field. -/
def CompleteHenselianValuedFieldStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [CompleteSpace K], IsHenselianValuedField K

end Langlands.AlgebraicGeometry.PointTopology
