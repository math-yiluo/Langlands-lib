import Langlands.AbelianScheme.Tate.GeometricTorsionReduction
import Langlands.AbelianScheme.Tate.GeometricTorsionNativeRank
import Langlands.AbelianScheme.MultiplicationDegree
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceStatement

/-! # Geometric torsion coordinates from ample existence and the cube theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

/-- Actual field torsion cardinality follows from algebraically closed ample
existence and the balanced cube theorem. Both geometric inputs are explicit. -/
theorem fieldTorsionCardinality_of_ample_and_cube
    (ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (cube : GroupScheme.FieldCubePullbackStatement.{u}) :
    FieldTorsionCardinalityStatement.{u} := by
  intro K _ _ B g hg n _hn hnK
  obtain ⟨L, hL⟩ := ample K B.toGrp B.smooth B.proper B.geometricallyConnected
  let x : Spec (CommRingCat.of K) := Classical.arbitrary _
  exact (natCard_level_eq_multiplicationFinrank_at_unit B n hnK x).trans
    (AbelianScheme.finrank_multiplication_eq_of_ne_zero B cube g hg L hL n hnK _)

/-- The unchanged relative target follows from the two remaining geometric
inputs; this conditional theorem does not discharge either input. -/
theorem geometricTorsionRank_of_ample_and_cube
    (ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (cube : GroupScheme.FieldCubePullbackStatement.{u}) :
    GeometricTorsionRankStatement.{u} :=
  geometricTorsionRank_of_fieldTorsionCardinality
    (fieldTorsionCardinality_of_ample_and_cube ample cube)

/-- Choose coordinates on actual geometric torsion from the two geometric
theorems, preserving its existing residue action. -/
def geometricTorsionLinearEquivOfGeometry
    (ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (cube : GroupScheme.FieldCubePullbackStatement.{u})
    (S : Scheme.{u}) (A : AbelianScheme S) (g : ℕ)
    (hg : A.HasRelativeDimension g) (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : Γ(S, ⊤)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ S) :
    (Fin (2 * g) → ZMod n) ≃ₗ[ZMod n]
      GroupScheme.Tate.Level A.toGrp (Over.mk s) n :=
  Classical.choice
    (geometricTorsionRank_of_ample_and_cube ample cube S A g hg n hn hunit Ω s).1

end Langlands.AbelianScheme.Tate
