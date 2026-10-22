import Langlands.Geometry.Analytic.RationalSpectrum.Definitions

/-! # Spectrum identification target for rational presentations -/

universe u

namespace Langlands.Analytic.RationalPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra BanachSpectrum

/-- Algebraic fractions are dense in the rational quotient; under the explicit
unit-ideal condition its spectrum is exactly the prescribed closed norm locus. -/
def SpectrumIdentificationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
    (g : StrictTateAlgebra (Fin n) K) (f : Fin m → StrictTateAlgebra (Fin n) K),
    Dense (fractionSubalgebra K (baseMap K n m S g f).toAlgHom
      (presentationMap K (ofRelations K n S) g) : Set (algebra K n m S g f)) ∧
    (GeneratesUnitIdeal K n m S g f →
      Set.range (comap (baseMap K n m S g f).toBoundedRingHom) = locus K n m S g f ∧
      Topology.IsClosedEmbedding (comap (baseMap K n m S g f).toBoundedRingHom))

end Langlands.Analytic.RationalPresentation
