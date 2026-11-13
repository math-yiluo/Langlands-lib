import Langlands.Representation.Intertwining.PQCompositionHaarReduction
import Langlands.Representation.Intertwining.PQCompositionProductDecomposition

/-! # Renard VII.3.5 (i): existence of compatible Haar measures -/

universe u

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Clause 1 of Renard VII.3.5 (i) on its own: Haar measures on `N̄₁ ∩ N₂`, `N̄₂ ∩ N₃` and
`N̄₁ ∩ N₃` compatible with the product decomposition exist. It is the published reduction
`pqCompositionHaarOfProduct` applied to the published product decomposition
`pqCompositionProduct`. -/
theorem pqCompositionHaar : PQCompositionHaarStatement.{u} :=
  pqCompositionHaarOfProduct pqCompositionProduct

end Langlands.Aubert.General.RepresentedParabolic
