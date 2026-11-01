import Langlands.Algebra.RenardNilpotentIdealFiltration
import Langlands.Algebra.RenardNilpotentDimensionMaximum

universe u

namespace Langlands.Renard

/-- Renard C.I: an actual maximizing tuple and its complement dimension bound. -/
def NilpotentMaximizingComplementStatement : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (l : ℕ),
    ∃ a : Fin l → Module.End ℂ V,
      (∀ i j, Commute (a i) (a j)) ∧
      (∀ i, IsNilpotent (a i)) ∧
      Module.finrank ℂ (NilpotentFiltration.generatedAlgebra a) =
        nilpotentGeneratedPhi l (Module.finrank ℂ V) ∧
      (∃ W : Submodule ℂ V,
        IsCompl (NilpotentFiltration.idealPowerSubspace a 1) W) ∧
      ∀ W : Submodule ℂ V,
        IsCompl (NilpotentFiltration.idealPowerSubspace a 1) W →
        nilpotentGeneratedPhi l (Module.finrank ℂ V) ≤
          Module.finrank ℂ W * Module.finrank ℂ V

end Langlands.Renard
