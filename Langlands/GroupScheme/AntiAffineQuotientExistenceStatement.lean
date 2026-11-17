import Langlands.GroupScheme.AntiAffine

/-! # Existence of the anti-affine affinization quotient -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every smooth connected field group admits its canonical affine quotient
with smooth connected anti-affine kernel. -/
def AntiAffineQuotientExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → ConnectedSpace G.X.left → Nonempty (AntiAffineQuotient G)

end Langlands.GroupScheme
