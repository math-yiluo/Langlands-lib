import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.Split

/-! # Split torus quotients of solvable groups over algebraically closed fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected solvable affine group over an algebraically closed field admits an
actual represented fppf quotient onto a split torus, with smooth connected normal unipotent
kernel. This is the quotient-existence part of Milne 2017, Theorem 16.33(a), (c), together
with splitting of tori over an algebraically closed field. This declaration is a proposition
target. -/
def SolvableTorusQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
    IsSolvableGroupScheme H →
    ∃ (U D : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ H) (q : H ⟶ D),
      IsClosedSubgroup i ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ IsUnipotent U ∧
        (SubgroupFunctor.range i).IsNormal ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧ IsSplitTorus D

end Langlands.GroupScheme
