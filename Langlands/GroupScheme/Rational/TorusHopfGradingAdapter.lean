import Langlands.GroupScheme.Rational.TorusGradedHopf
import Langlands.GroupScheme.Rational.HopfCoordinateComparison

/-! # The actual Hopf grading for a torus action without zero Lie weights -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusGradedHopf

variable {k : Type u} [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom H.X.hom] [IsAffine H.X.left]
  (hSmooth : Smooth H.X.hom)
  (S : CommGroupScheme (Spec (CommRingCat.of k)))
  (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp H)
  (hb : RelativeRoot.actionWeightSpace b 0 = ⊥)

include hSmooth hS b hb in
/-- A split-torus action without zero Lie weights supplies an integer grading
of the actual coordinate Hopf algebra, with its degree-zero augmentation in
the square of the augmentation ideal. -/
theorem exists_graded_of_noZeroWeight :
    ∃ (𝒜 : ℤ → Submodule k (AffineCoordinates.hopfAlgebra H)) (_ : GradedAlgebra 𝒜),
      Langlands.Algebra.GradedHopf.IsGradedBialgebra 𝒜 ∧
      ∀ a ∈ 𝒜 0, Bialgebra.counitAlgHom k (AffineCoordinates.hopfAlgebra H) a = 0 →
        a ∈ RingHom.ker (Bialgebra.counitAlgHom k (AffineCoordinates.hopfAlgebra H)) ^ 2 := by
  let _ : Smooth H.X.hom := hSmooth
  exact exists_grading_of_coordinate_equiv
    (AffineCoordinates.lieCoordinateAlgEquiv H)
    (TorusUnipotence.coordComul H) (TorusUnipotence.coordCounit H)
    (AffineCoordinates.lieCoordinateAlgEquiv_comul H)
    (AffineCoordinates.lieCoordinateAlgEquiv_counit H)
    (exists_coordinate_grading H hS b hb)

/-- A chosen integer grading on the actual coordinate Hopf algebra. -/
def gradingOfNoZeroWeight : ℤ → Submodule k (AffineCoordinates.hopfAlgebra H) :=
  (exists_graded_of_noZeroWeight H hSmooth S hS b hb).choose

/-- The chosen grading is an algebra grading. -/
@[instance_reducible]
def gradedAlgebraOfNoZeroWeight :
    GradedAlgebra (gradingOfNoZeroWeight H hSmooth S hS b hb) :=
  (exists_graded_of_noZeroWeight H hSmooth S hS b hb).choose_spec.choose

/-- The chosen grading has homogeneous Hopf structure maps and the required
degree-zero augmentation-square property. -/
theorem gradingOfNoZeroWeight_spec :
    Langlands.Algebra.GradedHopf.IsGradedBialgebra
        (gradingOfNoZeroWeight H hSmooth S hS b hb) ∧
      ∀ a ∈ gradingOfNoZeroWeight H hSmooth S hS b hb 0,
        Bialgebra.counitAlgHom k (AffineCoordinates.hopfAlgebra H) a = 0 →
        a ∈ RingHom.ker (Bialgebra.counitAlgHom k (AffineCoordinates.hopfAlgebra H)) ^ 2 :=
  (exists_graded_of_noZeroWeight H hSmooth S hS b hb).choose_spec.choose_spec

end Langlands.GroupScheme.TorusGradedHopf
