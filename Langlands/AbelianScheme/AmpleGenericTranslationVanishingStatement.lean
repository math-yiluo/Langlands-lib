import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # An ample base-point-free line bundle whose zero sets are generically preserved by a
translation forces the translation to be trivial -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Let `A` be an abelian scheme over an algebraically closed field `K` and `N` an ample
line bundle on `A` without rational base points. Let `x` be a rational point and `U` a
nonempty open subset of `A`. If for every rational point `y` lying in `U`, every global
section of `N` vanishing at `y` also vanishes at `x * y`, then `x` is the unit.
This proposition is a statement target, not a proof. -/
def AmpleGenericTranslationVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (N : LineBundle A.X.left),
    N.IsAmple →
    (∀ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X,
      ∃ σ : Langlands.SchemeModule.GlobalSections N.obj, ¬ VanishesAlong N y.left σ) →
    ∀ (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) (U : A.X.left.Opens),
      (U : Set A.X.left).Nonempty →
      (∀ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X,
        y.left (IsLocalRing.closedPoint K) ∈ U →
        ∀ σ : Langlands.SchemeModule.GlobalSections N.obj,
          VanishesAlong N y.left σ → VanishesAlong N (x * y).left σ) →
      x = 1

end Langlands.AbelianScheme
