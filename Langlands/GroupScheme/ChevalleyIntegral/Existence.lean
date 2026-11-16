import Langlands.GroupScheme.ChevalleyIntegral.FieldCellOpen
import Langlands.GroupScheme.ChevalleyIntegral.ClosureSmoothness

/-! # A single integral reductive realization of a finite reduced root datum -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- Every finite reduced root datum has a single integral reductive realization
with a closed coordinate torus and a common full root datum on all field fibres. -/
theorem chevalleyIntegralExistence : ChevalleyIntegralExistenceStatement.{u} := by
  apply ChevalleyIntegral.integralExistence_of_smoothClosure
  intro I J _ _ _ P _ b D
  classical
  let : Fintype J := Fintype.ofFinite J
  exact ChevalleyIntegral.integerModel_isSmooth D

end Langlands.GroupScheme
