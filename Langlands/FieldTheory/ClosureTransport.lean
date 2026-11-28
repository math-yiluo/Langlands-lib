import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed

/-! # Transport of closure properties across field isomorphisms -/

namespace Langlands.FieldTheory

universe u v

/-- Separable closedness transfers along a ring isomorphism of fields. -/
theorem isSepClosed_of_ringEquiv {k K : Type*} [Field k] [Field K] (e : k ≃+* K)
    [IsSepClosed k] : IsSepClosed K := by
  apply IsSepClosed.of_exists_root
  intro p hmon hirr hsep
  have hdeg : (p.map e.symm.toRingHom).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hirr)
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root (p.map e.symm.toRingHom) hdeg hsep.map
  refine ⟨e x, ?_⟩
  rw [Polynomial.IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hdeg hirr hsep hmon
  induction p using Polynomial.induction_on <;> simp_all

/-- Algebraic closure transfers through a ring equivalence even when the
fields have different universes. -/
theorem isAlgClosed_of_ringEquiv {A : Type v} [Field A] [IsAlgClosed A]
    (B : Type u) [Field B] (e : A ≃+* B) : IsAlgClosed B := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : (p.map e.symm.toRingHom).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hp)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (k := A) (p.map e.symm.toRingHom) hpe
  refine ⟨e x, ?_⟩
  rw [Polynomial.IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

end Langlands.FieldTheory
