import Langlands.Representation.IntegerLattice.GeneralizedWeightBlock

/-! # Actual generalized-weight support and common eigenvectors -/

set_option autoImplicit false

namespace Langlands

universe u

open IntegerLattice

/-- A unit label occurs in the actual generalized-weight support exactly when
the original tuple has a common nonzero eigenvector at that label. -/
def CommutingTupleGeneralizedWeightSupportStatement : Prop :=
  ∀ (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ),
    generalizedWeightBlock A c ≠ ⊥ ↔
      ∃ v : V, v ≠ 0 ∧ ∀ i : Fin d, (A.1 i : Module.End ℂ V) v = (c i : ℂ) • v

end Langlands
