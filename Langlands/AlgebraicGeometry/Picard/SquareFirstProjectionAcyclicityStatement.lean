import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Total acyclicity from acyclicity on the fibres of the first projection
of an abelian square over an algebraically closed field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Let `A` be an abelian scheme over an algebraically closed field `K` and `Q` a line
bundle on `A ×_K A`. If the restriction of `Q` to every fibre `{x} × A` of the first
projection, with `x` a `K`-rational point, has vanishing cohomology in every degree,
then `Q` has vanishing cohomology on `A ×_K A` in every degree.
This proposition is a statement target, not a proof. -/
def AlgClosedFieldSquareFirstProjectionAcyclicityStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K))),
    let Z : Scheme.{u} := pullback A.X.hom A.X.hom
    let sZ : Z ⟶ Spec (CommRingCat.of K) := pullback.fst A.X.hom A.X.hom ≫ A.X.hom
    let i₁ : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) → (A.X.left ⟶ Z) := fun x ↦
      pullback.lift (A.X.hom ≫ x.left) (𝟙 A.X.left) (by simp [Category.assoc, x.w])
    ∀ Q : LineBundle Z,
      (∀ (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) (n : ℕ),
        IsZero ((relativeCohomology A.X.hom n).obj
          ((LineBundle.pullback (i₁ x)).obj Q).obj)) →
      ∀ n : ℕ, IsZero ((relativeCohomology sZ n).obj Q.obj)

end Langlands.AbelianScheme
