import Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceOfFLT
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete

/-! # Proof of proper coherent formal existence over complete local rings -/

universe u

namespace Langlands.AlgebraicGeometry.Modules

/-- A compatible system of locally finitely presented module sheaves on the
maximal-ideal thickenings of a proper scheme over a complete local noetherian
ring has a locally finitely presented algebraization. The reduction
`properFormalCoherentExistence_of_flt` is applied to the ported existence
theorem for coherent module presheaves of the Anthropic formalization of
Fermat's Last Theorem. -/
theorem properFormalCoherentExistence : ProperFormalCoherentExistenceStatement.{u} :=
  ProperFormalCoherentExistenceOfFLT.properFormalCoherentExistence_of_flt
    _root_.AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete

end Langlands.AlgebraicGeometry.Modules
