import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix

/-!
# Local maximality of the orthogonal and unitary matrix groups

This proposition records an internal local input for maximality of the standard
archimedean compact subgroup. It does not prove the maximality assertion.
-/

universe u

namespace Langlands.Group

/-- A compact subgroup of matrix units containing every unitary matrix consists
entirely of unitary matrices. The field universe is arbitrary and rank zero is included. -/
def UnitaryMatrixCompactOvergroupStatement (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : Prop :=
  ∀ U : Subgroup (Matrix.GeneralLinearGroup (Fin n) 𝕜),
    IsCompact (U : Set (Matrix.GeneralLinearGroup (Fin n) 𝕜)) →
      (∀ q : Matrix.unitaryGroup (Fin n) 𝕜, Unitary.toUnits q ∈ U) →
        ∀ g ∈ U, (g : Matrix (Fin n) (Fin n) 𝕜) ∈ Matrix.unitaryGroup (Fin n) 𝕜

end Langlands.Group
