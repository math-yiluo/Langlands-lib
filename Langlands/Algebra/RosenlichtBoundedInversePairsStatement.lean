import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Finiteness.Basic

universe u v

namespace Langlands.Algebra

/-- Normalized inverse pairs in two finite-dimensional spaces form a finite set. -/
def RosenlichtBoundedInversePairsStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (B : Type v) [CommRing B] [Algebra k B] [IsDomain B]
    (epsilon : B →ₐ[k] k) (V W : Submodule k B)
    [Module.Finite k V] [Module.Finite k W],
    Set.Finite {p : B × B | p.1 ∈ V ∧ p.2 ∈ W ∧ p.1 * p.2 = 1 ∧
      epsilon p.1 = 1 ∧ epsilon p.2 = 1}

end Langlands.Algebra
