import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

namespace Langlands

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A continuous complex quasicharacter of a nonarchimedean group has open kernel. -/
def ContinuousComplexCharacterOpenKernel : Prop :=
  ∀ [NonarchimedeanGroup G] (chi : G →* ℂˣ),
    Continuous chi → IsOpen (chi.ker : Set G)

end Langlands
