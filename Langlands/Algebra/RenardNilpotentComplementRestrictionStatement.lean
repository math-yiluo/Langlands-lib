import Langlands.Algebra.RenardNilpotentIdealFiltration
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Nilpotent.Defs

universe u

namespace Langlands.Renard

/-- Renard C.I: restriction to a complement of `I V` is injective and bounds `dim R`. -/
def NilpotentComplementRestrictionStatement : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (l : ℕ) (a : Fin l → Module.End ℂ V),
    (∀ i j, Commute (a i) (a j)) →
    (∀ i, IsNilpotent (a i)) →
    ∀ (W : Submodule ℂ V),
      IsCompl (NilpotentFiltration.idealPowerSubspace a 1) W →
      Function.Injective
        (fun r : NilpotentFiltration.generatedAlgebra a =>
          (r : Module.End ℂ V).domRestrict W) ∧
      Module.finrank ℂ (NilpotentFiltration.generatedAlgebra a) ≤
        Module.finrank ℂ W * Module.finrank ℂ V

end Langlands.Renard
