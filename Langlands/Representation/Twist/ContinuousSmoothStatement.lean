import Langlands.Representation.Twist.Definitions
import Langlands.Representation.Smooth.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

namespace Langlands

universe uG uV

variable {G : Type uG} {V : Type uV}
variable [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

/-- Continuous complex twists preserve smooth vectors and smooth representations. -/
def ContinuousComplexTwistSmoothCompatibility : Prop :=
  ∀ [NonarchimedeanGroup G] (chi : G →* ℂˣ) (rho : Representation ℂ G V),
    Continuous chi →
      (∀ v : V, IsSmoothVector (twist chi rho) v ↔ IsSmoothVector rho v) ∧
      (IsSmooth (twist chi rho) ↔ IsSmooth rho)

end Langlands
