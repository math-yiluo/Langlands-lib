import Langlands.Representation.Smooth.Definitions
import Mathlib.RingTheory.Noetherian.Defs

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

variable [TopologicalSpace G]

/-- Proposition target for replacing all open subgroups by a cofinal family. -/
def AdmissibleCofinalStatement : Prop :=
  ∀ [IsNoetherianRing R] (S : Set (OpenSubgroup G)),
    (∀ K : OpenSubgroup G, ∃ L ∈ S, L ≤ K) →
    ∀ ρ : Representation R G V,
      IsAdmissible ρ ↔
        IsSmooth ρ ∧ ∀ K ∈ S, Module.Finite R (fixedVectors ρ K.toSubgroup)

end Langlands
