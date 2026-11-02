import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Torus.WeightDecomposition

/-! # The weight decomposition statement for the actual adjoint representation -/

noncomputable section
universe u

namespace Langlands.GroupScheme

/-- **Weight decomposition.** The Lie algebra of an affine group scheme locally of finite
type over a field is the internal direct sum of its weight spaces for any split torus. -/
theorem weightDecompositionStatement : WeightDecompositionStatement.{u} := by
  intro k _ G _ _ T hT i
  exact isInternal_weightSpace_of_isSplitTorus k G T hT i

end Langlands.GroupScheme
