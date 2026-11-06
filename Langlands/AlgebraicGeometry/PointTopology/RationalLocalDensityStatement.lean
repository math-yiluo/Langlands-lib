import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.NumberTheory.LocalField.Basic

/-! # Local Zariski density of actual rational points -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Evaluation at the unique point of the field spectrum is continuous, and
every nonempty analytic open set has Zariski-dense image. -/
def RationalLocalDensityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (X : Over (Spec (CommRingCat.of F))) [IsAffine X.left]
    [Smooth X.hom] [IsIntegral X.left],
    letI : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X
    Continuous (fun p : RationalPoint F X => p.left (IsLocalRing.closedPoint F)) ∧
      ∀ U : Set (RationalPoint F X), IsOpen U → U.Nonempty →
        Dense ((fun p : RationalPoint F X => p.left (IsLocalRing.closedPoint F)) '' U)

end Langlands.AlgebraicGeometry.PointTopology
