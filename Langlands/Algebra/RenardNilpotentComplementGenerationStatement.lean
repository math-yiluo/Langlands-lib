import Langlands.Algebra.RenardNilpotentIdealFiltration
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Nilpotent.Defs

universe u

namespace Langlands.Renard

/-- Renard C.I: a complement to `I V` generates each filtration quotient and `V`. -/
def NilpotentComplementGenerationStatement : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (l : ℕ) (a : Fin l → Module.End ℂ V),
    (∀ i j, Commute (a i) (a j)) →
    (∀ i, IsNilpotent (a i)) →
    ∀ (W : Submodule ℂ V),
      IsCompl (NilpotentFiltration.idealPowerSubspace a 1) W →
      (∀ n : ℕ, NilpotentFiltration.idealPowerSubspace a n =
        Submodule.span ℂ
          {v : V | ∃ (r : NilpotentFiltration.generatedAlgebra a) (w : W),
            r ∈ (NilpotentFiltration.generatorIdeal a) ^ n ∧
            (r : Module.End ℂ V) (w : V) = v} ⊔
        NilpotentFiltration.idealPowerSubspace a (n + 1)) ∧
      Submodule.span (NilpotentFiltration.generatedAlgebra a) (W : Set V) = ⊤

end Langlands.Renard
