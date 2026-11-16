import Langlands.Geometry.Analytic.GeneralizedAffinoid.Domain
import Langlands.Geometry.Analytic.Spectrum.ResidueField.Lift

/-! # Completed residue comparison for full affinoid domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

/-- A map representing a full affinoid domain induces a surjective canonical
map of completed residue fields at every point of its domain algebra. -/
def DomainCompletedResidueSurjectivityStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A B : PresentedAffinoidAlgebra K) (f : BoundedAlgHom K A B)
    (U : Set (BanachSpectrum A)),
    Represents K f U →
    ∀ y : BanachSpectrum B, Function.Surjective (BanachSpectrum.completedResidueComap K f y)

end Langlands.Analytic.PresentedAffinoidAlgebra
