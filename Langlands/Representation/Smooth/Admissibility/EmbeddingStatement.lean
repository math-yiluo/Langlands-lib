import Langlands.Representation.Smooth.Definitions
import Mathlib.RingTheory.Noetherian.Defs

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- An independently selectable target including its Noetherian hypothesis. -/
def AdmissibleSubrepresentationStatement : Prop :=
  ∀ [IsNoetherianRing R] (ρ : Representation R G V) (σ : Representation R G W)
    (f : ρ.IntertwiningMap σ),
    Function.Injective f → IsAdmissible σ → IsAdmissible ρ

end Langlands
