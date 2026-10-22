import Langlands.Geometry.Analytic.Spectrum.Definitions
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff

/-! # Exact target for the concrete multiplicative spectrum foundations -/

universe u v w

namespace Langlands.Analytic

open scoped Topology

/-- Compactness, separation, prime kernels, scalar normalization, functorial
inequality loci, and finite positive-threshold compact neighborhoods of the
actual multiplicative spectrum. Nonemptiness and domain representation are
not included. -/
def SpectrumPropertiesStatement : Prop :=
  (∀ (A : Type u) [NormedCommRing A],
    Topology.IsClosedEmbedding (fun x : BanachSpectrum A => (x : A → ℝ)) ∧
    T2Space (BanachSpectrum A) ∧ CompactSpace (BanachSpectrum A) ∧
    (∀ x : BanachSpectrum A, x.kernel.IsPrime) ∧
    (∀ (K : Type v) [NormedField K] [NormedAlgebra K A]
      (x : BanachSpectrum A) (c : K), x (algebraMap K A c) = ‖c‖) ∧
    (∀ (ι : Type v) (κ : Type w) (f : ι → A) (r : ι → ℝ)
      (g : κ → A) (s : κ → ℝ),
      IsClosed (BanachSpectrum.laurentLocus f r g s) ∧
        IsCompact (BanachSpectrum.laurentLocus f r g s)) ∧
    (∀ (x : BanachSpectrum A) (U : Set (BanachSpectrum A)), U ∈ 𝓝 x →
      ∃ (s t : Finset A) (r : s → ℝ) (q : t → ℝ),
        (∀ i, 0 < r i) ∧ (∀ j, 0 < q j) ∧
        IsCompact (BanachSpectrum.laurentLocus (fun i : s => i.val) r
          (fun j : t => j.val) q) ∧
        x ∈ interior (BanachSpectrum.laurentLocus (fun i : s => i.val) r
          (fun j : t => j.val) q) ∧
        BanachSpectrum.laurentLocus (fun i : s => i.val) r
          (fun j : t => j.val) q ⊆ U)) ∧
  (∀ (K : Type u) [NormedField K], ∀ (x : BanachSpectrum K) (a : K), x a = ‖a‖) ∧
  (∀ (A : Type u) [NormedCommRing A] (B : Type v) [NormedCommRing B]
    (φ : BoundedRingHom A B) (ι κ : Type w) (f : ι → A) (r : ι → ℝ)
    (g : κ → A) (s : κ → ℝ),
    BanachSpectrum.comap φ ⁻¹' BanachSpectrum.laurentLocus f r g s =
      BanachSpectrum.laurentLocus (φ ∘ f) r (φ ∘ g) s)

end Langlands.Analytic
