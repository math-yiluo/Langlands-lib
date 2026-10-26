import Langlands.Algebra.DirectedModuleSystem
import Mathlib.RingTheory.Flat.Basic

/-! # Eventual flatness ascends through a varying-ring directed colimit -/

universe uI uA uN uR uM

namespace Langlands.Algebra

/-- Internal flatness ascent for actual directed ring and additive colimit comparisons. -/
def DirectedModuleFlatnessAscentStatement : Prop :=
  ∀ (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
    (D : DirectedModuleSystem.{uI, uA, uN, uR, uM} ι R M),
    D.IsColimit →
    (∃ i₀, ∀ j, i₀ ≤ j → Module.Flat (D.base j) (D.obj j)) →
    Module.Flat R M

end Langlands.Algebra
