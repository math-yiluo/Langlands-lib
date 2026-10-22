import Langlands.Representation.Twist.Definitions
import Langlands.Representation.Smooth.Definitions
import Mathlib.RingTheory.Noetherian.Basic

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- Fixed vectors agree on subgroups in the character kernel, and an open-kernel
twist preserves admissibility over a Noetherian coefficient ring. -/
def TwistAdmissibilityCompatibility : Prop :=
  (∀ (chi : G →* Rˣ) (rho : Representation R G V) (H : Subgroup G),
    H ≤ chi.ker → fixedVectors (twist chi rho) H = fixedVectors rho H) ∧
  (∀ [TopologicalSpace G] [IsNoetherianRing R]
    (chi : G →* Rˣ) (rho : Representation R G V),
    IsOpen (chi.ker : Set G) →
      (IsAdmissible (twist chi rho) ↔ IsAdmissible rho))

end Langlands
