import Langlands.Representation.Smooth.Definitions

/-!
# Smoothness and continuity of discrete orbit maps

Statement of Renard III.1.1's unnumbered continuity characterization,
generalized to arbitrary commutative coefficient rings and topological groups.
-/

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V]

/-- A vector is smooth exactly when its orbit map into the discrete module is
continuous; all orbit maps are continuous exactly when the representation is
smooth. The module topology is specified inside the proposition. -/
def SmoothDiscreteOrbitStatement : Prop :=
  ∀ [IsTopologicalGroup G] (ρ : Representation R G V),
    letI : TopologicalSpace V := ⊥
    (∀ v : V, IsSmoothVector ρ v ↔ Continuous (fun g : G => ρ g v)) ∧
      (IsSmooth ρ ↔ ∀ v : V, Continuous (fun g : G => ρ g v))

end Langlands
