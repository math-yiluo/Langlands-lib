import Langlands.AbelianScheme.AlgClosedIsogenyPoints
import Langlands.AbelianScheme.Tate.AbelianPrimeAdic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Determinant

/-! # The p-adic norm of an actual Tate determinant and the point kernel -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

/-- The determinant of the actual rational Tate action measures the p-primary
part of the actual point kernel. This is an unproved proposition. -/
def GeometricTateDeterminantKernelStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Spec (CommRingCat.of k)))
    (p : ℕ) [Fact p.Prime] (f : End A),
    ‖LinearMap.det (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p f)‖ =
      ‖(Nat.card (GroupScheme.pointsHom (groupHom f) (Over.mk (𝟙 _))).ker : ℚ_[p])‖

end Langlands.AbelianScheme
