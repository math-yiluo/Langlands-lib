import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalPresentation
import Langlands.Geometry.Analytic.RationalSpectrum.Definitions

/-! # Spectrum identification target for weighted rational presentations -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation

/-- Algebraic fractions are dense in the actual weighted rational quotient.
Under unit-ideal generation its spectrum maps homeomorphically onto the
prescribed weighted locus, expressed by exact range and closed embedding.
No coefficient completeness is assumed. -/
def SpectrumIdentificationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K]
    (A : PresentedAffinoidAlgebra K) (m : ℕ) (s : PositivePolyradius (Fin m))
    (g : GeneralizedTateAlgebra A.polyradius K)
    (f : Fin m → GeneralizedTateAlgebra A.polyradius K),
    Dense (fractionSubalgebra K (baseMap K A s g f).toAlgHom
      (presentationMap K A g) : Set (algebra K A s g f)) ∧
    (GeneratesUnitIdeal K A g f →
      Set.range (spectrumMap K A s g f) = locus K A s g f ∧
      Topology.IsClosedEmbedding (spectrumMap K A s g f))

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation
