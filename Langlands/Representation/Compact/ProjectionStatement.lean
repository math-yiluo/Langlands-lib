import Langlands.Representation.Compact.Definitions

namespace Langlands.Compact

universe uG uV uW

/-- Compact averaging is a projection onto fixed vectors and is natural in the
smooth representation. This is a proposition target, not an asserted theorem. -/
def ProjectionAndNaturality : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
    LinearMap.IsProj (fixedVectors ρ K.toSubgroup) (averageMap ρ hρ K hK) ∧
    ∀ f : ρ.IntertwiningMap σ,
      f.toLinearMap.comp (averageMap ρ hρ K hK) =
        (averageMap σ hσ K hK).comp f.toLinearMap

end Langlands.Compact
