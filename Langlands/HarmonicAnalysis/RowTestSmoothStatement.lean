import Langlands.HarmonicAnalysis.Basic
import Langlands.Group.GL.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open stabilizers of Schwartz–Bruhat row test functions

This internal topological statement supplies the test-function smoothness
needed for finite compact-group reductions of Rankin–Selberg integrals.
-/

namespace Langlands.HarmonicAnalysis

universe uF

/-- Every compactly supported locally constant row function is fixed by an
open subgroup under right matrix multiplication. -/
def RowTestSmoothStatement (F : Type uF) [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] (n : ℕ) : Prop :=
  ∀ Φ : SchwartzBruhat (Fin n → F),
    ∃ U : OpenSubgroup (Langlands.GeneralLinear n F),
      ∀ g ∈ U, ∀ x : Fin n → F, Φ (Matrix.vecMul x g.val) = Φ x

end Langlands.HarmonicAnalysis
