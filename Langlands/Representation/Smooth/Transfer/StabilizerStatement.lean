import Langlands.Representation.Smooth.Definitions
import Mathlib.RepresentationTheory.Stabilizer

/-! Proposition target identifying smooth vectors by their open stabilizers. -/

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V]

/-- A smooth vector is exactly a vector with an open stabilizer. -/
def SmoothVectorStabilizerStatement : Prop :=
  ∀ [IsTopologicalGroup G] (ρ : Representation R G V) (v : V),
    IsSmoothVector ρ v ↔ IsOpen (ρ.stabilizer v : Set G)

end Langlands
