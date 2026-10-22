import Langlands.Representation.Smooth.Definitions

/-! Proposition target for smoothness transfer along intertwiners. -/

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Smoothness passes to an equivariantly embedded representation and to an
equivariant quotient. No exactness assertion about invariant submodules is made. -/
def SmoothSubquotientStatement : Prop :=
  ∀ (ρ : Representation R G V) (σ : Representation R G W)
    (f : ρ.IntertwiningMap σ),
    (Function.Injective f → IsSmooth σ → IsSmooth ρ) ∧
    (Function.Surjective f → IsSmooth ρ → IsSmooth σ)

end Langlands
