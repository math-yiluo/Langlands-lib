import Langlands.GroupScheme.Rational.CoordinateCotangent
import Mathlib.Algebra.DirectSum.Module

/-! # Split-torus decomposition targets for actual augmentation coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

open Classical in
/-- Splitness gives actual coordinate and augmentation decompositions, and the
augmentation quotient lifts each cotangent eigenvector at the same character. -/
def CoordinateWeightDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hAff : IsAffineHom G.X.hom) (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ b : AutomorphicAction S.toGrp G,
    letI := hAff
    DirectSum.IsInternal (weightSpace b) ∧
    DirectSum.IsInternal (augmentationWeightSpace b) ∧
    DirectSum.IsInternal (cotangentWeightSpace b) ∧
    (∀ χ : characterLattice S,
      (augmentationWeightSpace b χ).map (cotangentMk G) = cotangentWeightSpace b χ)

end Langlands.GroupScheme.CoordinateWeights
