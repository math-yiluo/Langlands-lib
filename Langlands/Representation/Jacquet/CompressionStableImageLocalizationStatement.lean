import Langlands.Algebra.RenardEndomorphismLocalization
import Langlands.Representation.Jacquet.StableCompressionPower
import Mathlib.LinearAlgebra.Projection

/-! # Localization at a stabilized compact compression

The localization clause of Renard 2026, VI.9.1, Proposition, printed page
197 / PDF page 203. The preceding stabilization conclusions are the
hypothesis `CompactCompressionStationaryFrom`.
-/

set_option autoImplicit false

universe uG uV

namespace Langlands.Jacquet

open Renard.EndomorphismLocalization

/-- Once the compact compression has stationary power chains and complementary
limits, localization at the compression is canonically its stable image with
the restricted action. The canonical localization map becomes projection
onto that image along the power-kernel supremum. -/
def CompressionStableImageLocalizationStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) (b : ℕ)
    (h : CompactCompressionStationaryFrom ρ hρ K hK g b),
    let C := compressedAction ρ hρ K hK g
    let S := stableImage ρ hρ K hK g
    let D := powerKernelSup ρ hρ K hK g
    ∃! e : Localized C ≃ₗ[ℂ] S,
      e.toLinearMap.comp (localizedEnd C) =
        (stableImageAction ρ hρ K hK g).comp e.toLinearMap ∧
      e.toLinearMap.comp (iota C) = S.projectionOnto D h.2.symm

end Langlands.Jacquet
