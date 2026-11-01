import Langlands.Algebra.RenardNilpotentHeadTailRestriction
import Langlands.Algebra.RenardNilpotentDimensionMaximum

universe u

namespace Langlands.Renard

/-- Renard C.I: the actual head/tail splitting and first-level dimension comparisons. -/
def NilpotentHeadTailDimensionStatement : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (l : ℕ) (a : Fin (l + 1) → Module.End ℂ V),
    (∀ i j, Commute (a i) (a j)) →
    (∀ i, IsNilpotent (a i)) →
    (NilpotentFiltration.tailAlgebra a).toSubmodule ⊔
        NilpotentFiltration.headIdealSubspace a = ⊤ ∧
    Module.finrank ℂ (NilpotentFiltration.tailAlgebra a) ≤
      nilpotentGeneratedPhi l (Module.finrank ℂ V) ∧
    Module.finrank ℂ (NilpotentFiltration.headIdealSubspace a) ≤
      Module.finrank ℂ (NilpotentFiltration.firstLevelAlgebra a) ∧
    Module.finrank ℂ (NilpotentFiltration.firstLevelAlgebra a) ≤
      nilpotentGeneratedPhi (l + 1)
        (Module.finrank ℂ (NilpotentFiltration.idealPowerSubspace a 1)) ∧
    ∀ (W : Submodule ℂ V),
      IsCompl (NilpotentFiltration.idealPowerSubspace a 1) W →
      Module.finrank ℂ (NilpotentFiltration.generatedAlgebra a) ≤
        nilpotentGeneratedPhi l (Module.finrank ℂ V) +
        nilpotentGeneratedPhi (l + 1)
          (Module.finrank ℂ V - Module.finrank ℂ W)

end Langlands.Renard
