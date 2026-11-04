import Langlands.AlgebraicGeometry.PointTopology.StandardEtalePoints

/-! # Openness of actual point maps in a standard etale presentation -/

universe u v w

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The local standard etale input for smooth point-map openness. -/
def StandardEtalePointOpenStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A]
    (B : Type w) [CommRing B] [Algebra K B] [Algebra A B]
    [IsScalarTower K A B] (_P : StandardEtalePresentation A B),
    IsOpenMap (AlgPoint.precomp (S := K) (IsScalarTower.toAlgHom K A B))

end Langlands.AlgebraicGeometry.PointTopology
