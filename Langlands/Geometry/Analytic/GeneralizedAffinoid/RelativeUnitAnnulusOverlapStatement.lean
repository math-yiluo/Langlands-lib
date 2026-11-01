import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeUnitAnnulus

/-! # The actual overlap as a closed principal quotient of the unit annulus -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus

/-- The canonical overlap map presents the actual overlap by the closed `x-f` relation. -/
def OverlapPresentationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : PresentedAffinoidAlgebra K) (f : A),
    Function.Surjective (toOverlap K A f) ∧
      RingHom.ker (toOverlap K A f).toAlgHom =
        (Ideal.span ({annulusX K A - baseMap K A f} : Set (Algebra K A))).closure ∧
      ∀ (o : BinaryLaurent.Overlap K A f) (ε : ℝ), 0 < ε →
        ∃ z : Algebra K A, toOverlap K A f z = o ∧ ‖z‖ < ‖o‖ + ε

end Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus
