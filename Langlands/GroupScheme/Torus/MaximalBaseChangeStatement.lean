import Langlands.GroupScheme.Torus.Maximal

/-! # Statement: maximality of tori under field extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A closed torus in a smooth affine group is maximal exactly when its base
change to a field extension is maximal (Milne, Theorem 17.82). -/
def MaximalTorusBaseChangeStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
    IsTorus T.toGrp → IsClosedSubgroup i →
      (IsMaximalTorus i ↔
        IsMaximalTorus
          (T := (CommGroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
          ((GroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i))

end Langlands.GroupScheme
