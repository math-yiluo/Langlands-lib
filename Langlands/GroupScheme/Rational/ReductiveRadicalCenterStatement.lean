import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.ReducedSubgroupAction

/-! # The solvable radical and the reduced identity component of the centre -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The geometric solvable radical of a connected reductive field group is a
central torus. Over the algebraic closure it is the reduced identity
component of the scheme-theoretic centre, as an embedded subgroup. -/
def ReductiveRadicalCenterStatement : Prop :=
  ∀ (k : Type u) [Field k] (G R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G)
    (hG : IsConnectedReductive G), IsGeometricSolvableRadical r →
    IsTorus R ∧ IsCentral r ∧
      let B := GroupScheme.baseChange (toAlgebraicClosure k)
      ∀ (Z : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))))
        (z : Z ⟶ B.obj G) (hz : IsSchemeTheoreticCenter z),
        letI : IsClosedImmersion z.hom.hom.left := hz.1
        letI : Smooth (B.obj G).X.hom := hG.baseChange_toAlgebraicClosure.smooth
        letI : IsAffineHom (B.obj G).X.hom := hG.baseChange_toAlgebraicClosure.isAffineHom
        letI : LocallyOfFiniteType Z.X.hom := by
          rw [← Over.w z.hom.hom]
          infer_instance
        letI : IsAffineHom Z.X.hom := by
          rw [← Over.w z.hom.hom]
          infer_instance
        SubgroupFunctor.range (B.map r) =
          SubgroupFunctor.range (ReducedSubgroup.identityCoreι Z ≫ z)

end Langlands.GroupScheme
