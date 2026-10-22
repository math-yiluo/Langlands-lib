import Langlands.Geometry.Analytic.WeierstrassPresentation.Definitions

/-! # Spectrum identification target for Weierstrass presentations -/

universe u

namespace Langlands.Analytic.WeierstrassPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra BanachSpectrum

/-- The constructed Weierstrass quotient has a dense base image and its spectrum
is a closed subspace with exactly the prescribed unit-radius point locus. -/
def SpectrumIdentificationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
    (f : Fin m → StrictTateAlgebra (Fin n) K),
    DenseRange (baseMap K n m S f) ∧
    Set.range (comap (baseMap K n m S f).toBoundedRingHom) = locus K n m S f ∧
    Topology.IsClosedEmbedding (comap (baseMap K n m S f).toBoundedRingHom)

end Langlands.Analytic.WeierstrassPresentation
