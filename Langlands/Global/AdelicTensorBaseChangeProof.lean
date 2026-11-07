import Langlands.Global.AdelicTensorBaseChangeStatement
import Langlands.Global.CurvePlaceAdeleTensorComparison
import Langlands.Global.NumberFieldAdeleTensorComparison

/-! # The canonical full adelic tensor comparison in both characteristics -/

noncomputable section

universe u

namespace Langlands.Global

/-- The canonical full adelic tensor maps are bijective in both characteristics. -/
theorem adelicTensorBaseChangeProof : AdelicTensorBaseChangeStatement.{u} := by
  exact ⟨curvePlaceAdeleTensorMap_bijective, numberFieldAdeleTensorMap_bijective⟩

end Langlands.Global
