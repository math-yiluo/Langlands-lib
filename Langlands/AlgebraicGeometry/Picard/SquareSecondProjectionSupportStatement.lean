import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.SquareSecondFibre
import Langlands.AlgebraicGeometry.Modules.ModuleSupport
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Finite support from rational-fibre vanishing on the second square projection -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules

/-- All-degree fibre cohomology vanishing outside a finite set of rational points
gives finite closed support for every second-projection higher direct image.
This proposition is a statement target, not a proof. -/
def SquareSecondProjectionSupportStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K)))
    (Q : LineBundle (pullback A.X.hom A.X.hom))
    (F : Set (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)),
    F.Finite →
    (∀ x, x ∉ F → ∀ n : ℕ,
      IsZero ((DerivedSections.relativeCohomology A.X.hom n).obj
        ((LineBundle.pullback (squareSecondInclusion A.X.hom x.left x.w)).obj Q).obj)) →
    ∀ n : ℕ, HasFiniteClosedSupport
      ((DerivedSections.higherDirectImage (pullback.snd A.X.hom A.X.hom) n).obj Q.obj)

end Langlands.AbelianScheme
