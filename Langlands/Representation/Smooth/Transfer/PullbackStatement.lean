import Langlands.Representation.Smooth.Definitions

/-! Proposition target for smoothness under continuous pullback. -/

namespace Langlands

universe uR uG uV uH

variable {R : Type uR} {G : Type uG} {V : Type uV} {H : Type uH}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [Group H] [TopologicalSpace H]

/-- Pullback along a continuous group homomorphism preserves smoothness. -/
def SmoothPullbackStatement : Prop :=
  ∀ (ρ : Representation R G V) (φ : H →* G),
    Continuous φ → IsSmooth ρ → IsSmooth (ρ.comp φ)

end Langlands
