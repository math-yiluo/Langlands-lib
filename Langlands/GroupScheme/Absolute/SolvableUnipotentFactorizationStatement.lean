import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.Characters

/-! # Rational unipotent-times-torus factorization of solvable groups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, let `B` be a smooth connected affine solvable group and
`t : T ⟶ B` any supplied maximal torus. Then `B` has a smooth connected normal unipotent closed
subgroup `a : U ⟶ B` such that every base point of `B` is a product `a(v) * t(s)` of a base
point `v` of `U` and a base point `s` of `T`, in this order. This is the base-point consequence
of Milne 2017, Theorem 16.33(a), (c), (d). -/
def SolvableUnipotentFactorizationStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (B : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left],
    IsSolvableGroupScheme B →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ B),
      IsMaximalTorus t →
      ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (a : U ⟶ B),
        IsClosedSubgroup a ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧
          IsUnipotent U ∧ (SubgroupFunctor.range a).IsNormal ∧
          ∀ b : rationalPoints B,
            ∃ (v : rationalPoints U) (s : rationalPoints T.toGrp),
              (v ≫ a.hom.hom) * (s ≫ t.hom.hom) = b

end Langlands.GroupScheme
