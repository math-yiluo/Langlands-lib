import Langlands.GroupScheme.Torus.Maximal

/-! # Statement: a trivial maximal torus over an algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, a smooth connected affine group with a
trivial maximal torus is unipotent. -/
def AlgClosedTrivialMaximalTorusUnipotentStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
    IsMaximalTorus i → SubgroupFunctor.range i = ⊥ → IsUnipotent G

end Langlands.GroupScheme
