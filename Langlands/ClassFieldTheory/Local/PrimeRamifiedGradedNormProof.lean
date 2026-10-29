import Langlands.ClassFieldTheory.Local.PrimeGradedNormFromArithmeticProof
import Langlands.ClassFieldTheory.Local.PrimeRamifiedTraceIdealsProof
import Langlands.ClassFieldTheory.Local.PrimeNormTraceExpansionProof

/-! The closed prime ramified graded norm theorem. -/

namespace Langlands.LocalClassField

/-- All prime ramified graded norm formulas with their literal coefficients. -/
theorem primeRamifiedGradedNorm.{u,v} : PrimeRamifiedGradedNorm.{u,v} :=
  primeGradedNormFromArithmetic.{u,v}
    primeRamifiedTraceIdeals.{u,v} primeNormTraceExpansion.{u,v}

end Langlands.LocalClassField
