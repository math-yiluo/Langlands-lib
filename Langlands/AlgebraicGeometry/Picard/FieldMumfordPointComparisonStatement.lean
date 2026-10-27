import Langlands.AlgebraicGeometry.Picard.MumfordBundle

/-! # The rigidified Mumford comparison at field-valued points -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- For an abelian scheme `A` over a field `k`, a field point `a : Spec K → A`
over `b : Spec K → Spec k` and the section `x` of `A_K` lying over `a`: if the
underlying bundle of a rigidified family `Q` over `Spec K` is isomorphic to
`t_x^*L_K ⊗ M_K`, then the rigidified pullback of the Mumford family along `a`
is isomorphic to `Q`. This declaration states the proposition. -/
def FieldMumfordPointComparisonStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (k : Type u) [Field k] (A : AbelianScheme (Spec (CommRingCat.of k)))
    (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left)
    (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (a : Over.mk b ⟶ A.X)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((baseChange b).obj A).X),
    x.left ≫ pullback.fst A.X.hom b = a.left →
    ∀ (Q : RigidifiedFamily A (Over.mk b)),
      Nonempty (LineBundle.tensor preservation
          ((LineBundle.pullback
            (GroupScheme.translation ((baseChange b).obj A).toGrp x).left).obj
              ((LineBundle.pullback (pullback.fst A.X.hom b)).obj
                ((RigidifiedLineBundle.forget (unitSection A)).obj L)))
          ((LineBundle.pullback (pullback.fst A.X.hom b)).obj M) ≅
        familyLineBundle A (T := Over.mk b) Q) →
      Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) (T := Over.mk b) a).obj
            (mumfordBundle A preservation L M evaluation) ≅ Q)

end Langlands.AbelianScheme
