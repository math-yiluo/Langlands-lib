import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Affine base change of a line bundle with zero higher direct images -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- For a smooth proper morphism and an actual line bundle, vanishing of every
higher direct image implies cohomology vanishing after every affine base change.
This definition states a proposition and does not prove it. -/
def HigherDirectImageVanishingAffineBaseChangeStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    Smooth f → IsProper f →
    ∀ Q : Picard.LineBundle X,
      (∀ n : ℕ, IsZero ((DerivedSections.higherDirectImage f n).obj Q.obj)) →
      ∀ (R : CommRingCat.{u}) (x : Spec R ⟶ Y) (n : ℕ),
        IsZero
          ((DerivedSections.relativeCohomology (pullback.snd f x) n).obj
            ((Scheme.Modules.pullback (pullback.fst f x)).obj Q.obj))

end Langlands.AlgebraicGeometry.Modules
