import Langlands.LinearAlgebra.CartanCNumbering

/-! # Rigidity of the numbered Cartan matrix of type B -/

namespace Langlands

/-- A numbering identifies every entry of the supplied matrix with type B. -/
def IsTypeBNumbering {ι : Type*} (M : Matrix ι ι ℤ) {n : ℕ}
    (e : ι ≃ Fin n) : Prop :=
  ∀ a b, M a b = CartanMatrix.B n (e a) (e b)

namespace CartanBNumbering

/-- The type-B Cartan entry is the reversed type-C entry. -/
theorem apply_eq_C {n : ℕ} (i j : Fin n) :
    CartanMatrix.B n i j = CartanMatrix.C n j i := by
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M i j)
    (CartanMatrix.C_transpose n) |>.symm

/-- A map preserving all type-B Cartan entries fixes every vertex. -/
theorem rigid {n : ℕ} (hn : 2 ≤ n) (f : Fin n → Fin n)
    (hf : ∀ i j, CartanMatrix.B n (f i) (f j) = CartanMatrix.B n i j) :
    ∀ i, f i = i := by
  apply CartanCNumbering.rigid hn f
  intro i j
  simpa only [apply_eq_C] using hf j i

/-- A type-B numbering of a fixed matrix is unique. -/
theorem unique {ι : Type*} {M : Matrix ι ι ℤ} {n : ℕ} (hn : 2 ≤ n)
    (e f : ι ≃ Fin n) (he : IsTypeBNumbering M e) (hf : IsTypeBNumbering M f) :
    e = f := by
  have hrigid := rigid hn (fun i => f (e.symm i)) (fun i j => by
    rw [← hf, he]
    simp)
  apply Equiv.ext
  intro a
  simpa using (hrigid (e a)).symm

end CartanBNumbering

end Langlands
