import Langlands.Geometry.Analytic.Spectrum.SpectralJointContinuityStatement

/-! # Joint spectrum pullback continuity from uniform spectral displacement -/

universe u v w

namespace Langlands.Analytic.BanachSpectrum

open Filter
open scoped Topology

/-- Uniform spectral control of each element's displacement implies joint
continuity of the concrete bounded-map pullback on spectra. -/
theorem spectralParametricPullbackContinuity :
    SpectralParametricPullbackContinuityStatement.{u, v, w} := by
  intro A _ B _ T _ f hf
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  change Continuous (fun p : T × BanachSpectrum B => p.2 (f p.1 a))
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, x₀⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht := (continuous_fst.tendsto (t₀, x₀))
    (hf a t₀ (ε / 2) (half_pos hε))
  have hx := Metric.tendsto_nhds.mp
    (((evaluation (f t₀ a)).continuous.comp continuous_snd).tendsto (t₀, x₀))
      (ε / 2) (half_pos hε)
  filter_upwards [ht, hx] with p hp hpx
  change dist (p.2 (f t₀ a)) (x₀ (f t₀ a)) < ε / 2 at hpx
  have hd : dist (p.2 (f p.1 a)) (p.2 (f t₀ a)) ≤ ε / 2 := by
    rw [Real.dist_eq]
    exact (abs_sub_map_le_sub p.2.toMulRingSeminorm _ _).trans (hp p.2)
  calc
    dist (p.2 (f p.1 a)) (x₀ (f t₀ a)) ≤
      dist (p.2 (f p.1 a)) (p.2 (f t₀ a)) +
      dist (p.2 (f t₀ a)) (x₀ (f t₀ a)) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hd hpx
    _ = ε := add_halves ε

end Langlands.Analytic.BanachSpectrum
