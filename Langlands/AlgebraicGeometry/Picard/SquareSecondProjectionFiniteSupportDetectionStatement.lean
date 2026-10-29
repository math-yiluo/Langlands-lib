import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Finite-support cohomology detection for the second square projection -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules

/-- For a line bundle on an abelian square over an algebraically closed field,
vanishing of all total cohomology and of all second-projection fibre cohomology
outside finitely many rational points forces vanishing on every fibre.
This is a statement target, not a proof. -/
def AlgClosedFieldSquareSecondProjectionFiniteSupportDetectionStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K)))
    (Q : LineBundle (pullback A.X.hom A.X.hom))
    (F : Set (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)),
    let sZ := pullback.fst A.X.hom A.X.hom ≫ A.X.hom
    let i2 : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) →
        (A.X.left ⟶ pullback A.X.hom A.X.hom) :=
      fun x ↦ pullback.lift (𝟙 A.X.left) (A.X.hom ≫ x.left) (by
        have hx : x.left ≫ A.X.hom = 𝟙 _ := x.w
        simp [Category.assoc, hx])
    F.Finite →
      (∀ x, x ∉ F → ∀ n : ℕ,
        IsZero ((DerivedSections.relativeCohomology A.X.hom n).obj
          ((LineBundle.pullback (i2 x)).obj Q).obj)) →
      (∀ n : ℕ, IsZero ((DerivedSections.relativeCohomology sZ n).obj Q.obj)) →
      ∀ x (n : ℕ),
        IsZero ((DerivedSections.relativeCohomology A.X.hom n).obj
          ((LineBundle.pullback (i2 x)).obj Q).obj)

end Langlands.AbelianScheme
