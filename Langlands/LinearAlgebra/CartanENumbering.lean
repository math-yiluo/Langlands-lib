import Langlands.LinearAlgebra.CartanWalkColor

/-! # Rigidity of the numbered E8 Cartan matrix -/

namespace Langlands.CartanENumbering

open CartanWalkColor

theorem eq_two_iff {n : ℕ} (i j : Fin n) :
    CartanMatrix.E n i j = 2 ↔ i = j := by
  simp only [CartanMatrix.E, Matrix.of_apply]
  split_ifs <;> simp_all

theorem injective_of_preserves {n : ℕ} (f : Fin n → Fin n)
    (hf : ∀ i j, CartanMatrix.E n (f i) (f j) = CartanMatrix.E n i j) :
    Function.Injective f := by
  intro i j hij
  apply (eq_two_iff i j).mp
  rw [← hf, hij]
  exact (eq_two_iff _ _).mpr rfl

/-- Three adjacency walk refinements distinguish all eight vertices. -/
theorem rigid_eight (f : Fin 8 → Fin 8)
    (hf : ∀ i j, CartanMatrix.E 8 (f i) (f j) = CartanMatrix.E 8 i j) :
    ∀ i, f i = i := by
  have hbij : Function.Bijective f :=
    (Finite.injective_iff_bijective).mp (injective_of_preserves f hf)
  have h1 : step (CartanMatrix.E 8) (fun _ => 1) =
      ![1, 1, 2, 3, 2, 2, 2, 1] := by decide
  have h2 : step (CartanMatrix.E 8) ![1, 1, 2, 3, 2, 2, 2, 1] =
      ![2, 3, 4, 5, 5, 4, 3, 2] := by decide
  have h3 : step (CartanMatrix.E 8) ![2, 3, 4, 5, 5, 4, 3, 2] =
      ![4, 5, 7, 12, 9, 8, 6, 3] := by decide
  have hi1 := step_invariant hf hbij (c := fun _ => 1) (fun _ => rfl)
  rw [h1] at hi1
  have hi2 := step_invariant hf hbij hi1
  rw [h2] at hi2
  have hi3 := step_invariant hf hbij hi2
  rw [h3] at hi3
  have hinj : Function.Injective (![4, 5, 7, 12, 9, 8, 6, 3] : Fin 8 → ℕ) := by
    decide
  intro i
  exact hinj (hi3 i)

end Langlands.CartanENumbering
