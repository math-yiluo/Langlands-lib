import Langlands.GroupScheme.Trigonalizable
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.FieldTheory.Separable

/-! # Groups that become trigonalizable over a separable extension (Milne 16.6) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Theorem 16.6: an affine algebraic group `G` over a field `k` becomes
trigonalizable over a separable algebraic extension of `k` if and only if it has a normal
unipotent closed subgroup `U` with a fppf quotient `G ⟶ M` by `U` onto a group of multiplicative
type. For every such `U`, every unipotent closed subgroup of `G` is contained in `U`; in
particular `U` is unique. -/
def SeparablyTrigonalizableCriterionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    ((∃ (K : Type u) (_ : Field K) (_ : Algebra k K), Algebra.IsSeparable k K ∧
        IsTrigonalizable
          ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) ↔
      ∃ (U M : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G) (q : G ⟶ M),
        IsClosedSubgroup i ∧ IsUnipotent U ∧ (SubgroupFunctor.range i).IsNormal ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧ IsMultiplicativeType M) ∧
    ∀ (U M : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G) (q : G ⟶ M),
      IsClosedSubgroup i → IsUnipotent U → (SubgroupFunctor.range i).IsNormal →
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q → IsMultiplicativeType M →
        ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G),
          IsClosedSubgroup j → IsUnipotent V →
            SubgroupFunctor.range j ≤ SubgroupFunctor.range i

end Langlands.GroupScheme
