import Langlands.GroupScheme.AntiAffine

/-! # Geometry of a supplied group affinization -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A supplied affinization of a smooth connected field group has smooth connected
finite-type affine target and a faithfully flat quasi-compact projection. -/
def AffinizationGeometryStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
    Smooth G.X.hom → ConnectedSpace G.X.left → IsAffinization q →
      Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧
      Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧ QuasiCompact q.hom.hom.left

end Langlands.GroupScheme
