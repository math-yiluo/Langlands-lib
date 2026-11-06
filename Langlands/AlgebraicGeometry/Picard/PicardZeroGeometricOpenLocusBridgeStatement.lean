import Langlands.AlgebraicGeometry.Picard.OpenLocus
import Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricDetectionStatement

/-! # From a geometric-point Picard-zero locus to the all-test criterion -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Geometric detection upgrades a supplied geometric-point locus to the existing
Picard-zero open-locus criterion on every test scheme over an arbitrary base. -/
def PicardZeroGeometricOpenLocusBridgeStatement : Prop :=
  PicardZeroGeometricDetectionStatement.{u} →
    ∀ {S : Scheme.{u}} (A : AbelianScheme S) {P : Over S}
      (L : RigidifiedFamily A P) (U : P.left.Opens),
      (∀ (K : Type u) [Field K] [IsAlgClosed K]
        (s : Spec (CommRingCat.of K) ⟶ P.left),
        IsPicardZeroFamily A
          ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
            (unitSection_comp A)
            (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L) ↔
          Set.range s ⊆ (U : Set P.left)) →
        IsPicardZeroOpenLocus A L U

end Langlands.AbelianScheme
