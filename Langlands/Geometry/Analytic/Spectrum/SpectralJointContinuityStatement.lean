import Langlands.Geometry.Analytic.Spectrum.Definitions

/-! # Spectral displacement control for parametric spectrum pullbacks -/

universe u v w

namespace Langlands.Analytic.BanachSpectrum

open scoped Topology

/-- Uniform spectral smallness of the displacement of each fixed element,
locally at every parameter, implies joint continuity of the actual pullback
on bounded multiplicative spectra. No norm continuity or common norm bound
on the family of bounded ring maps is assumed. -/
def SpectralParametricPullbackContinuityStatement : Prop :=
  ∀ (A : Type u) [NormedCommRing A] (B : Type v) [NormedCommRing B]
    (T : Type w) [TopologicalSpace T] (f : T → BoundedRingHom A B),
    (∀ (a : A) (t₀ : T) (ε : ℝ), 0 < ε →
      ∀ᶠ t in 𝓝 t₀, ∀ x : BanachSpectrum B,
        x (f t a - f t₀ a) ≤ ε) →
    Continuous (fun p : T × BanachSpectrum B => comap (f p.1) p.2)

end Langlands.Analytic.BanachSpectrum
