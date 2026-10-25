import Langlands.AlgebraicGeometry.Picard.RelativePicardZero

/-! # Geometric-point detection for actual rigidified Picard-zero families -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The geometric Picard-zero condition is detected by actual rigidified pullbacks
to spectra of algebraically closed fields in the same universe. -/
def PicardZeroGeometricDetectionStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (T : Over S) (L : RigidifiedFamily A T),
    IsPicardZeroFamily A L ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (s : Spec (CommRingCat.of K) ⟶ T.left),
        IsPicardZeroFamily A
          ((RigidifiedLineBundle.relativePullback A.X.hom
            (unitSection A) (unitSection_comp A)
            (Over.homMk s rfl : Over.mk (s ≫ T.hom) ⟶ T)).obj L)

end Langlands.AbelianScheme
