import Langlands.AbelianScheme.CotangentBaseChangeStatement
import Langlands.AlgebraicGeometry.ModuleDualPullback

/-! # Canonical Lie base change for abelian schemes -/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace Langlands.AbelianScheme

/-- Arbitrary base change for the relative Lie module of an abelian scheme,
identified by the actual cotangent and dual pullback comparisons. -/
def LieBaseChangeStatement (S : AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ (T : AlgebraicGeometry.Scheme.{u}) (b : T ⟶ S) (A : AbelianScheme S),
    IsIso (GroupScheme.cotangentBaseChangeMap b A.toGrp) ∧
      ∃ ell : (pullback b).obj A.Lie ≅ ((baseChange b).obj A).Lie,
        ell.hom ≫ Langlands.Scheme.Modules.dualMap
            (GroupScheme.cotangentBaseChangeMap b A.toGrp) =
          Langlands.Scheme.Modules.dualPullbackComparison b
            (GroupScheme.cotangentAtIdentity A.toGrp)

end Langlands.AbelianScheme
