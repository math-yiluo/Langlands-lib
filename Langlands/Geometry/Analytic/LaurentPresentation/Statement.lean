import Langlands.Geometry.Analytic.LaurentPresentation.Definitions

/-! # Spectrum identification target for a Laurent presentation -/

universe u

namespace Langlands.Analytic.LaurentPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra BanachSpectrum

/-- The explicit common-denominator rational quotient has precisely the
unit-radius Laurent locus as its spectrum image, with a closed embedding. -/
def SpectrumIdentificationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n m l : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
    (f : Fin m → StrictTateAlgebra (Fin n) K)
    (g : Fin l → StrictTateAlgebra (Fin n) K),
    RationalPresentation.GeneratesUnitIdeal K n (m + l + 1) S
      (denominator K n l g) (numerators K n m l f g) ∧
    RationalPresentation.locus K n (m + l + 1) S
      (denominator K n l g) (numerators K n m l f g) = locus K n m l S f g ∧
    Set.range (comap (baseMap K n m l S f g).toBoundedRingHom) = locus K n m l S f g ∧
    Topology.IsClosedEmbedding (comap (baseMap K n m l S f g).toBoundedRingHom) ∧
    IsCompact (locus K n m l S f g)

end Langlands.Analytic.LaurentPresentation
