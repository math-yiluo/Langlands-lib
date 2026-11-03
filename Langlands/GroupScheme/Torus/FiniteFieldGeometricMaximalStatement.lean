import Langlands.GroupScheme.Torus.Maximal

/-! # Statement: geometrically maximal tori over finite fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected affine group over a finite field contains a torus whose
algebraic-closure base change is maximal. -/
def FiniteFieldGeometricMaximalTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalTorus i ∧
        IsMaximalTorus (T := (CommGroupScheme.baseChange (toAlgebraicClosure k)).obj T)
          ((GroupScheme.baseChange (toAlgebraicClosure k)).map i)

end Langlands.GroupScheme
