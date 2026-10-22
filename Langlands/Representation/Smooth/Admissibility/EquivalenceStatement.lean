import Langlands.Representation.Smooth.Definitions

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Admissibility is invariant under equivalence of representations. -/
def AdmissibleEquivalenceStatement : Prop :=
  ∀ (ρ : Representation R G V) (σ : Representation R G W) (_e : ρ.Equiv σ),
    IsAdmissible ρ ↔ IsAdmissible σ

end Langlands
