import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Langlands.Global.AdelicFunctoriality.NormAssemblyProof

/-! # Unconditional local/global compatibility of the actual adelic norm -/

namespace Langlands.Global.AdelicFunctoriality

universe u v

/-- The canonical completed tensor comparisons and principal-adele norm identity. -/
theorem normCompatibility : NormCompatibility.{u, v} :=
  ⟨completedTensorComparison.{u, v},
    normAssembly.{u, v}.1 completedTensorComparison.{u, v}⟩

end Langlands.Global.AdelicFunctoriality
