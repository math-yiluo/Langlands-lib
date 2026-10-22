import Langlands.Representation.Smooth.Definitions

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- Increasing the subgroup decreases the fixed-vector submodule. -/
def FixedVectorsAntitoneStatement : Prop :=
  ∀ ρ : Representation R G V, Antitone (fixedVectors ρ)

end Langlands
