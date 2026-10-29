import Langlands.AlgebraicGeometry.ProjectiveSpace
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Separating line bundles on proper schemes over algebraically closed fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Very-ampleness criterion over an algebraically closed field: a proper scheme over `K`
carrying an actual line bundle whose complete linear system of global sections is
base-point free on rational points and separates rational points and nonzero
dual-number tangent vectors admits a closed immersion into some polynomial-Proj
projective space `ProjectiveSpace K n` over `Spec K`.
This proposition is a statement target, not a proof. -/
def SeparatingLineBundleHProjectivityStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of K)) (L : Picard.LineBundle X),
    IsProper p → Picard.SeparatesPointsAndTangents p L → IsHProjective p

end Langlands.AlgebraicGeometry
