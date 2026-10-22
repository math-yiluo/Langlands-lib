import Langlands.Geometry.Analytic.Spectrum.Quotient.Definitions

/-! # Exact target for spectra of closed-ideal quotients -/

universe u

namespace Langlands.Analytic

/-- Ideal zero loci are closed, and a closed ideal's actual quotient spectrum
embeds as precisely its zero locus, with a unique descended seminorm. -/
def QuotientSpectrumStatement : Prop :=
  ∀ (A : Type u) [NormedCommRing A],
    (∀ I : Ideal A, IsClosed (BanachSpectrum.zeroLocus I)) ∧
    (∀ (I : Ideal A) [IsClosed (I : Set A)],
      Topology.IsClosedEmbedding (BanachSpectrum.comap (BanachSpectrum.quotientHom I)) ∧
      Set.range (BanachSpectrum.comap (BanachSpectrum.quotientHom I)) =
        BanachSpectrum.zeroLocus I ∧
      ∀ (x : BanachSpectrum A), I ≤ x.kernel →
        ∃! y : BanachSpectrum (A ⧸ I), ∀ a : A, y (Ideal.Quotient.mk I a) = x a)

end Langlands.Analytic
