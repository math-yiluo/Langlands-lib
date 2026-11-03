import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! # Finite-type specialization with prescribed nonvanishing -/

universe u v

namespace Langlands.RingTheory

open scoped BigOperators

/-- A nonempty basic open in a finite-type algebra over an algebraically closed
field has a ground-field point, preserving each prescribed factor. -/
def FiniteTypeNonvanishingSpecializationStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (s : Finset A),
    ¬ IsNilpotent (∏ a ∈ s, a) →
      ∃ φ : A →ₐ[k] k, ∀ a ∈ s, φ a ≠ 0

end Langlands.RingTheory
