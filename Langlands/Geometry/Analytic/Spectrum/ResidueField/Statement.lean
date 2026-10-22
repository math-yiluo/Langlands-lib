import Langlands.Geometry.Analytic.Spectrum.ResidueField.Definitions

/-! # Exact evaluation in the constructed completed residue field -/

universe u v

namespace Langlands.Analytic

open BanachSpectrum

/-- The constructed completed residue field realizes the original spectrum
seminorm, has exactly its kernel, and is the completion of its fraction field. -/
def CompletedResidueFieldStatement : Prop :=
  ∀ (A : Type u) (K : Type v) [NormedCommRing A] [NormedField K]
    [IsUltrametricDist K] [NormedAlgebra K A] (x : BanachSpectrum A),
    (∀ a : A, ‖completedResidueMap K x a‖ = x a) ∧
    (∀ a : A, completedResidueMap K x a = 0 ↔ a ∈ x.kernel) ∧
    comap (completedResidueMap K x).toBoundedRingHom
      (fieldPoint (CompletedResidueField K x)) = x ∧
    Isometry (residueCompletionMap K x) ∧
    DenseRange (residueCompletionMap K x)

end Langlands.Analytic
