import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # Rigidity of the numbered Cartan matrix of type C -/

namespace Langlands

/-- A numbering identifies every entry of the supplied matrix with type C. -/
def IsTypeCNumbering {ι : Type*} (M : Matrix ι ι ℤ) {n : ℕ}
    (e : ι ≃ Fin n) : Prop :=
  ∀ a b, M a b = CartanMatrix.C n (e a) (e b)

namespace CartanCNumbering

theorem eq_two_iff {n : ℕ} (i j : Fin n) :
    CartanMatrix.C n i j = 2 ↔ i = j := by
  simp only [CartanMatrix.C, Matrix.of_apply]
  split_ifs <;> simp_all

theorem eq_neg_two_iff {n : ℕ} (i j : Fin n) :
    CartanMatrix.C n i j = -2 ↔ i.val = n - 1 ∧ j.val + 1 = i.val := by
  simp only [CartanMatrix.C, Matrix.of_apply]
  split_ifs <;> constructor <;> intro h <;> first | omega | simp_all

theorem adjacent_of_ne_zero {n : ℕ} {i j : Fin n} (hne : i ≠ j)
    (h : CartanMatrix.C n i j ≠ 0) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [CartanMatrix.C, Matrix.of_apply, ite_eq_right hne] at h
  split_ifs at h <;> simp_all

/-- A map preserving all type C Cartan entries fixes every vertex. -/
theorem rigid {n : ℕ} (hn : 2 ≤ n) (f : Fin n → Fin n)
    (hf : ∀ i j, CartanMatrix.C n (f i) (f j) = CartanMatrix.C n i j) :
    ∀ i, f i = i := by
  have hinj : Function.Injective f := by
    intro i j hij
    apply (eq_two_iff i j).mp
    rw [← hf, hij, CartanMatrix.C_diag]
  let last : Fin n := ⟨n - 1, by omega⟩
  let prev : Fin n := ⟨n - 2, by omega⟩
  have hlast : f last = last := by
    have h : CartanMatrix.C n (f last) (f prev) = -2 := by
      rw [hf]
      exact (eq_neg_two_iff last prev).mpr (by dsimp [last, prev]; omega)
    apply Fin.ext
    exact (eq_neg_two_iff (f last) (f prev)).mp h |>.1
  have hfix : ∀ k, ∀ i : Fin n, n - 1 - i.val = k → f i = i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hk
      by_cases hilast : i = last
      · simpa [hilast] using hlast
      have hi : i.val + 1 < n := by
        have : i.val ≠ n - 1 := fun h => hilast (Fin.ext h)
        omega
      let j : Fin n := ⟨i.val + 1, hi⟩
      have hjfix : f j = j := ih (n - 1 - j.val) (by dsimp [j]; omega) j rfl
      have hji : CartanMatrix.C n j i ≠ 0 := by
        simp only [CartanMatrix.C, Matrix.of_apply]
        split_ifs <;> dsimp [j] at * <;> omega
      have hadj := adjacent_of_ne_zero
        (show f j ≠ f i from fun h => by
          have := hinj h
          have := congrArg Fin.val this
          dsimp [j] at this
          omega)
        (show CartanMatrix.C n (f j) (f i) ≠ 0 by rw [hf]; exact hji)
      rw [hjfix] at hadj
      rcases hadj with hright | hleft
      · have hfi : (f i).val = i.val + 2 := by dsimp [j] at hright; omega
        let k' : Fin n := ⟨i.val + 2, by have := (f i).isLt; omega⟩
        have hk' : f k' = k' := ih (n - 1 - k'.val)
          (by dsimp [k']; omega) k' rfl
        have hsame : f i = f k' := by rw [hk']; exact Fin.ext hfi
        have := congrArg Fin.val (hinj hsame)
        dsimp [k'] at this
        omega
      · apply Fin.ext
        dsimp [j] at hleft
        omega
  intro i
  exact hfix _ i rfl

/-- A type C numbering of a fixed matrix is unique, including at rank two. -/
theorem unique {ι : Type*} {M : Matrix ι ι ℤ} {n : ℕ} (hn : 2 ≤ n)
    (e f : ι ≃ Fin n) (he : IsTypeCNumbering M e) (hf : IsTypeCNumbering M f) :
    e = f := by
  have hrigid := rigid hn (fun i => f (e.symm i)) (fun i j => by
    rw [← hf, he]
    simp)
  apply Equiv.ext
  intro a
  simpa using (hrigid (e a)).symm

end CartanCNumbering

end Langlands
