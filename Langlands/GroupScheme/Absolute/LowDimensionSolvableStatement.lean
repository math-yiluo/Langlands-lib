import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Lie.DimensionInduction

/-! # Statement: group varieties of dimension at most two are solvable -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Corollary 17.27. A smooth connected affine group over an algebraically
closed field whose dimension is at most `2` is solvable. For a smooth group the
dimension is measured by its Lie algebra. -/
def LowDimensionSolvableStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    Lie.dimension G ≤ 2 → IsSolvableGroupScheme G

end Langlands.GroupScheme
