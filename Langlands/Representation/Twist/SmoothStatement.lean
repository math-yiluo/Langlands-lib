import Langlands.Representation.Twist.Definitions
import Langlands.Representation.Smooth.Definitions

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V]

/-- An open-kernel character does not change which vectors are smooth. -/
def TwistSmoothCompatibility : Prop :=
  ∀ (chi : G →* Rˣ) (rho : Representation R G V),
    IsOpen (chi.ker : Set G) →
      (∀ v : V, IsSmoothVector (twist chi rho) v ↔ IsSmoothVector rho v) ∧
      (IsSmooth (twist chi rho) ↔ IsSmooth rho)

end Langlands
