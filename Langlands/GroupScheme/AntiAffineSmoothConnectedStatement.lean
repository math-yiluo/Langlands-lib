import Langlands.GroupScheme.AntiAffine

/-! # Smoothness and connectedness of anti-affine algebraic groups -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every anti-affine algebraic field group is smooth and connected. -/
def AntiAffineSmoothConnectedStatement : Prop :=
  ∀ (k : Type u) [Field k] (N : GroupScheme (Spec (CommRingCat.of k))),
    LocallyOfFiniteType N.X.hom → QuasiCompact N.X.hom → IsAntiAffine N →
      Smooth N.X.hom ∧ ConnectedSpace N.X.left

end Langlands.GroupScheme
