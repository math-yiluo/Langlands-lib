import Langlands.Cohomology.ModuleComplex.BoundedFlatQuasiIsoBaseChangeStatement
import Langlands.AnthropicFLT.Theorems.Thm_Module_quasiIso_baseChange_of_quasiIso_of_flat

set_option autoImplicit false

universe u

namespace Langlands.Cohomology.ModuleComplex

theorem boundedFlatQuasiIsoBaseChange : BoundedFlatQuasiIsoBaseChangeStatement.{u} := by
  exact Module.quasiIso_baseChange_of_quasiIso_of_flat

end Langlands.Cohomology.ModuleComplex
