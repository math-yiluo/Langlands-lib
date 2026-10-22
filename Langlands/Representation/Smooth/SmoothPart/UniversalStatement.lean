import Langlands.Representation.Smooth.SmoothPart.Definitions

/-! # Unique factorization through the smooth part: proposition target -/

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Every intertwiner from a smooth representation factors uniquely through
the smooth-part inclusion. -/
def SmoothPartUniversalProperty : Prop :=
  ∀ [IsTopologicalGroup G],
    ∀ (ρ : Representation R G V) (σ : Representation R G W),
      IsSmooth σ → ∀ f : σ.IntertwiningMap ρ,
        ∃! lift : σ.IntertwiningMap (smoothPart ρ), (smoothInclusion ρ).comp lift = f

end Langlands
