import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.TorusDominationBaseChange
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Torus quotients of split-torus-dominated solvable groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected affine solvable group with a pointed dominant
parametrization by a split torus has an actual torus fppf quotient with a
closed smooth connected unipotent full kernel over the same field. -/
def SplitTorusDominatedSolvableQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
    IsSolvableGroupScheme H → HasPointedSplitTorusDomination H →
      ∃ (U D : GroupScheme (Spec (CommRingCat.of k)))
        (i : U ⟶ H) (q : H ⟶ D),
        IsClosedSubgroup i ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧
          IsUnipotent U ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧ IsTorus D

end Langlands.GroupScheme
