import Langlands.Global.AdelicFunctoriality.NormAssemblyStatement
import Langlands.Global.AdelicFunctoriality.NormDescentReduction

/-! # Proof of the determinant and quotient-descent reductions -/

namespace Langlands.Global.AdelicFunctoriality

universe u v

/-- The principal-norm formula gives the unique continuous quotient norm. -/
theorem ideleClassNormDescent : IdeleClassNormDescent.{u, v} := by
  intro h K L _ _ _ _ _
  refine ⟨ideleClassNormOfPrincipalFormula (h K L), ?_, ?_⟩
  · intro a
    exact ideleClassNormOfPrincipalFormula_mk (h K L) a
  · intro f hf
    exact ideleClassNormOfPrincipalFormula_unique (h K L) f hf

/-- The remaining arithmetic input for assembly is the separate tensor comparison. -/
theorem normAssembly : NormAssembly.{u, v} :=
  ⟨principalNormCompatibility_of_completedTensorComparison, ideleClassNormDescent⟩

end Langlands.Global.AdelicFunctoriality
