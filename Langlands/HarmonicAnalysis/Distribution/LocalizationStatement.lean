import Langlands.HarmonicAnalysis.Distribution.Basic
import Mathlib.Topology.Separation.Profinite

/-!
# Localization of equivariant distributions along an invariant continuous map

This is the localization principle used in Bernstein–Zelevinsky (1976), §6.9
and §2.37, stated for the actual algebraic distributions of the Library.
-/

namespace Langlands.HarmonicAnalysis.Distribution

universe uX uY uI

/-- Localization principle: let `q : X → Y` be continuous into a Hausdorff,
locally compact, totally disconnected space, and let `h i` be homeomorphisms of
`X` preserving every fiber of `q`, with scalars `χ i`. If, for every `y`, every
distribution supported in the fiber `q ⁻¹ {y}` and satisfying
`(h i)_* T = χ i • T` for all `i` vanishes, then every distribution on `X`
satisfying these equivariance identities vanishes. -/
def EquivariantLocalizationStatement : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X]
    (Y : Type uY) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
      [TotallyDisconnectedSpace Y]
    (q : X → Y), Continuous q →
    ∀ (ι : Type uI) (h : ι → X ≃ₜ X) (χ : ι → ℂ),
      (∀ i x, q (h i x) = q x) →
      (∀ (y : Y) (T : Distribution X),
          (∀ f : SchwartzBruhat X, (∀ x, q x = y → f x = 0) → T f = 0) →
          (∀ i, pushforward (h i) T = χ i • T) → T = 0) →
      ∀ D : Distribution X, (∀ i, pushforward (h i) D = χ i • D) → D = 0

end Langlands.HarmonicAnalysis.Distribution
