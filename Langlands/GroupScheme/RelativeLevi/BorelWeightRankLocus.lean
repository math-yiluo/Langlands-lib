import Langlands.GroupScheme.RelativeLevi.BorelWeightRecognition
import Langlands.GroupScheme.Torus.GeometricAdjointWeightRanks

/-! # The clopen locus with no opposite nonzero adjoint weight ranks -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.splitTorus

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (P : GroupScheme (Spec (CommRingCat.of r))) [IsAffineHom P.X.hom]
  [Smooth P.X.hom] (f : splitTorus (Spec (CommRingCat.of r)) I ⟶ P)

/-- The points where the actual geometric adjoint weight profile has no
opposite nonzero entries away from the zero character. -/
def noOppositeWeightRankLocus : Set (Spec (CommRingCat.of r)) :=
  {s | ∀ m : I → ℤ, m ≠ 0 →
    geometricExponentWeightRankProfile I P f s m = 0 ∨
      geometricExponentWeightRankProfile I P f s (-m) = 0}

/-- Absence of opposite nonzero geometric adjoint weight ranks defines a
clopen locus over every affine base. -/
theorem isClopen_noOppositeWeightRankLocus :
    IsClopen (noOppositeWeightRankLocus I P f) := by
  have h := isLocallyConstant_geometricExponentWeightRankProfile I P f
  exact ⟨⟨h {p | ¬ ∀ m : I → ℤ, m ≠ 0 → p m = 0 ∨ p (-m) = 0}⟩,
    h {p | ∀ m : I → ℤ, m ≠ 0 → p m = 0 ∨ p (-m) = 0}⟩

end Langlands.GroupScheme.splitTorus
