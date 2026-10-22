import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# The intrinsic nonarchimedean prerequisite for actual general linear groups
-/

namespace Langlands

universe u

/-- Actual finite general linear groups over a valuative field are nonarchimedean. -/
def ValuativeGeneralLinearNonarchimedean : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsValuativeTopology K] (n : ℕ),
    NonarchimedeanGroup (Matrix.GeneralLinearGroup (Fin n) K)

end Langlands
