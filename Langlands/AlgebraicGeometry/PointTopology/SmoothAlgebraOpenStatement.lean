import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Analysis.Normed.Field.Basic

/-! # Smooth algebra maps on complete-field points -/

universe u v w

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The affine algebra-map step in Conrad's local smooth-openness assertion. -/
def SmoothAlgebraPointOpenStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A]
    (B : Type w) [CommRing B] [Algebra K B] [Algebra A B]
    [IsScalarTower K A B] [Algebra.Smooth A B],
      IsOpenMap (AlgPoint.precomp (S := K) (IsScalarTower.toAlgHom K A B))

end Langlands.AlgebraicGeometry.PointTopology
