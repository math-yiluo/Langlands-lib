import Langlands.Algebra.RenardNilpotentIdealFiltration
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Nilpotent.Defs

universe u

namespace Langlands.Renard

/-- Renard C.I: the actual ideal-power filtration vanishes at the ambient dimension. -/
def NilpotentFiltrationVanishingStatement : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (l : ℕ) (a : Fin l → Module.End ℂ V),
    (∀ i j, Commute (a i) (a j)) →
    (∀ i, IsNilpotent (a i)) →
    NilpotentFiltration.idealPowerSubspace a (Module.finrank ℂ V) = ⊥

end Langlands.Renard
