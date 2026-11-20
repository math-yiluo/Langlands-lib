import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # An ample base-point-free line bundle cannot have its zero sets generically tangent to
a nonzero translation-invariant vector field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Let `A` be an abelian scheme over an algebraically closed field `K` and `N` an ample
line bundle on `A` without rational base points. Let `t` be a nonzero rational tangent
vector at the unit and `U` a nonempty open subset of `A`. Then it is not the case that
for every rational point `y` lying in `U`, every global section of `N` vanishing at `y`
also vanishes along the translate `t ≫ τ_y` of `t` to `y`.
This proposition is a statement target, not a proof. -/
def AmpleGenericTangentVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (N : LineBundle A.X.left),
    N.IsAmple →
    (∀ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X,
      ∃ σ : Langlands.SchemeModule.GlobalSections N.obj, ¬ VanishesAlong N y.left σ) →
    ∀ (t : Spec (CommRingCat.of (DualNumber K)) ⟶ A.X.left),
      IsNonzeroTangentVectorAt A.X.hom
        (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X).left t →
    ∀ (U : A.X.left.Opens), (U : Set A.X.left).Nonempty →
      ¬ (∀ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X,
        y.left (IsLocalRing.closedPoint K) ∈ U →
        ∀ σ : Langlands.SchemeModule.GlobalSections N.obj,
          VanishesAlong N y.left σ →
            VanishesAlong N (t ≫ (GroupScheme.translation A.toGrp y).left) σ)

end Langlands.AbelianScheme
