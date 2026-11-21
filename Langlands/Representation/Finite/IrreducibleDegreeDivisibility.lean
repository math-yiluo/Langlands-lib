import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Divisibility of irreducible complex representation degrees

Serre, *Linear Representations of Finite Groups*, §6.5, Corollary 2.
-/

namespace Langlands

/-- The dimension of an irreducible complex representation of a finite
group divides the order of the group. -/
def IrreducibleDegreeDivisibilityStatement.{uG, uV} : Prop :=
  ∀ (G : Type uG) [Group G] [Finite G] (V : Type uV) [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V),
    ρ.IsIrreducible → Module.finrank ℂ V ∣ Nat.card G

end Langlands
