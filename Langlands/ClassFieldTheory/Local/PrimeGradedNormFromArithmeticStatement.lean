import Langlands.ClassFieldTheory.Local.PrimeRamifiedGradedNormStatement
import Langlands.ClassFieldTheory.Local.PrimeRamifiedTraceIdealsStatement
import Langlands.ClassFieldTheory.Local.PrimeNormTraceExpansionStatement

namespace Langlands.LocalClassField
universe u v

/-- The complete graded norm conclusion conditional on the two arithmetic inputs. -/
def PrimeGradedNormFromArithmetic : Prop :=
  PrimeRamifiedTraceIdeals.{u,v} → PrimeNormTraceExpansion.{u,v} →
    PrimeRamifiedGradedNorm.{u,v}

end Langlands.LocalClassField
