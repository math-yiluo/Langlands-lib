import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # One-dimensional connected group varieties are commutative -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 14.25: every connected affine group scheme over a
field that is smooth of relative dimension one is commutative. -/
def OneDimensionalCommutativeStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 G.X.hom] [IsAffineHom G.X.hom],
    ConnectedSpace G.X.left → IsCommMonObj G.X

end Langlands.GroupScheme
