import Langlands.Representation.Smooth.SmoothPart.Definitions

/-! # Basic properties of the smooth part: proposition target -/

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V]

/-- Closure, membership, action stability, and smoothness of the smooth part.
The topological-group hypothesis is needed only for the final group of clauses. -/
def SmoothPartBasicStatement : Prop :=
  ∀ ρ : Representation R G V,
    (∀ v : V, v ∈ smoothVectors ρ ↔ IsSmoothVector ρ v) ∧
    IsSmoothVector ρ 0 ∧
    (∀ v w : V, IsSmoothVector ρ v → IsSmoothVector ρ w → IsSmoothVector ρ (v + w)) ∧
    (∀ (a : R) (v : V), IsSmoothVector ρ v → IsSmoothVector ρ (a • v)) ∧
    (IsSmooth ρ ↔ smoothVectors ρ = ⊤) ∧
    (∀ [IsTopologicalGroup G],
      (∀ (g : G) (v : V), IsSmoothVector ρ v → IsSmoothVector ρ (ρ g v)) ∧
      IsSmooth (smoothPart ρ) ∧
      (∀ v : smoothVectors ρ, smoothInclusion ρ v = (v : V)) ∧
      Function.Injective (smoothInclusion ρ))

end Langlands
