import Langlands.Global.Adelic
import Langlands.Global.CompletionPadic

/-! # The existing finite completion as a nonarchimedean local field -/

noncomputable section

universe u

open NumberField
open scoped WithZero

namespace Langlands.Global.FiniteCompletion

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)

/-- The valuative relation defined by the existing completion valuation. -/
@[instance_reducible]
def valuativeRel : ValuativeRel (FiniteCompletion F v) :=
  ValuativeRel.ofValuation (Valued.v : Valuation (FiniteCompletion F v) ℤᵐ⁰)

theorem valuativeRel_vle (x y : FiniteCompletion F v) :
    @ValuativeRel.vle (FiniteCompletion F v) _ (valuativeRel v) x y ↔
      Valued.v x ≤ Valued.v y :=
  Iff.rfl

/-- The published p-adic realization has exactly this valuative relation. -/
theorem topologicalData_valuativeRel_eq :
    (CompletionPadic.topologicalData v).valuativeRel = valuativeRel v := by
  apply ValuativeRel.ext
  funext x y
  exact propext (CompletionPadic.topologicalData_vle v x y)

/-- The local-field certificate uses the existing completion topology. -/
theorem isNonarchimedeanLocalField :
    letI := valuativeRel v
    IsNonarchimedeanLocalField (FiniteCompletion F v) := by
  rw [← topologicalData_valuativeRel_eq v]
  exact (CompletionPadic.topologicalData v).localField

end Langlands.Global.FiniteCompletion
