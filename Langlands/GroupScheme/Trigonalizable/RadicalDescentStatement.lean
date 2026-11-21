import Langlands.GroupScheme.Trigonalizable.SeparableCriterionStatement
import Langlands.GroupScheme.Rational.SemistandardIntersection

/-! # Separable trigonalizability and descent of the geometric unipotent radical -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Corollary 16.31. A smooth connected affine solvable group over a field `k`
becomes trigonalizable over a separable algebraic extension of `k` if and only if its
geometric unipotent radical descends as a closed subgroup to `k`. -/
def SeparablyTrigonalizableRadicalDescentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsSolvableGroupScheme G →
    ((∃ (K : Type u) (_ : Field K) (_ : Algebra k K), Algebra.IsSeparable k K ∧
        IsTrigonalizable
          ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) ↔
      ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G), IsGeometricUnipotentRadical i)

end Langlands.GroupScheme
