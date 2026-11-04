import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Expressing a finite family through a linearly independent family -/

namespace Langlands.LinearAlgebra

/-- A finite family in an algebra over a field is a combination, with coefficients in the field,
of a finite linearly independent family: a basis of the span of the family. -/
theorem exists_linearIndependent_sum_algebraMap_mul {k A C : Type*} [Field k] [Ring A]
    [Algebra k A] [Finite C] (w : C → A) :
    ∃ (m : ℕ) (e : Fin m → A) (r : C → Fin m → k), LinearIndependent k e ∧
      ∀ κ, w κ = ∑ l, algebraMap k A (r κ l) * e l := by
  let V := Submodule.span k (Set.range w)
  have : FiniteDimensional k V := FiniteDimensional.span_of_finite k (Set.finite_range w)
  let b := Module.finBasis k V
  refine ⟨Module.finrank k V, fun l => (b l : A),
    fun κ l => b.repr ⟨w κ, Submodule.subset_span ⟨κ, rfl⟩⟩ l, ?_, ?_⟩
  · exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · intro κ
    have h := congrArg Subtype.val (b.sum_repr ⟨w κ, Submodule.subset_span ⟨κ, rfl⟩⟩)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul] at h
    simp only [← Algebra.smul_def]
    exact h.symm

end Langlands.LinearAlgebra
