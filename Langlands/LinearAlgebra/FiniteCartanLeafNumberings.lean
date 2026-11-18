import Langlands.LinearAlgebra.FiniteCartanExceptionalColumns
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Exact numberings for leaf extensions of the classical matrices -/

universe u v

open Matrix

namespace Langlands.LinearAlgebra.FiniteCartanMatrix

theorem hasCartanMatrix_congr {ι : Type u} {κ : Type v}
    {M : Matrix ι ι ℤ} {N : Matrix κ κ ℤ} (e : ι ≃ κ)
    (he : ∀ i j, M i j = N (e i) (e j)) {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℤ) :
    HasCartanMatrix M C ↔ HasCartanMatrix N C := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨e.symm.trans f, fun i j => ?_⟩
    simpa using (he (e.symm i) (e.symm j)).symm.trans (hf (e.symm i) (e.symm j))
  · rintro ⟨f, hf⟩
    exact ⟨e.trans f, fun i j => (he i j).trans (hf (e i) (e j))⟩

theorem hasIrreducibleCartanType_congr {ι : Type u} {κ : Type v}
    {M : Matrix ι ι ℤ} {N : Matrix κ κ ℤ} (e : ι ≃ κ)
    (he : ∀ i j, M i j = N (e i) (e j)) :
    HasIrreducibleCartanType M ↔ HasIrreducibleCartanType N := by
  simp only [HasIrreducibleCartanType, hasCartanMatrix_congr e he]

/-- Extend an equivalence on the old vertices, fixing the appended vertex. -/
def extendLastEquiv {n m : ℕ} (e : Fin n ≃ Fin m) : Fin (n + 1) ≃ Fin (m + 1) where
  toFun := Fin.lastCases (Fin.last m) (fun i => (e i).castSucc)
  invFun := Fin.lastCases (Fin.last n) (fun i => (e.symm i).castSucc)
  left_inv i := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv i := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] theorem extendLastEquiv_castSucc {n m : ℕ} (e : Fin n ≃ Fin m) (i : Fin n) :
    extendLastEquiv e i.castSucc = (e i).castSucc := by
  simp [extendLastEquiv]

@[simp] theorem extendLastEquiv_last {n m : ℕ} (e : Fin n ≃ Fin m) :
    extendLastEquiv e (Fin.last n) = Fin.last m := by
  simp [extendLastEquiv]

theorem leafExtension_A_reflect {n : ℕ} (k : Fin n) (a b : ℤ) :
    ∀ i j, leafExtension (CartanMatrix.A n) k a b i j =
      leafExtension (CartanMatrix.A n) k.rev a b
        (extendLastEquiv (Fin.revPerm (n := n)) i) (extendLastEquiv (Fin.revPerm (n := n)) j) := by
  intro i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [leafExtension, CartanMatrix.A, Fin.ext_iff] <;> grind

theorem leafExtension_A_last_eq_A {n : ℕ} (k : Fin n) (hk : k.val + 1 = n) :
    leafExtension (CartanMatrix.A n) k (-1) (-1) = CartanMatrix.A (n + 1) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [leafExtension, CartanMatrix.A, Fin.ext_iff] <;> grind

theorem leafExtension_A_last_eq_B {n : ℕ} (k : Fin n) (hk : k.val + 1 = n) :
    leafExtension (CartanMatrix.A n) k (-2) (-1) = CartanMatrix.B (n + 1) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [leafExtension, CartanMatrix.A, CartanMatrix.B, Fin.ext_iff] <;> grind

theorem leafExtension_A_last_eq_C {n : ℕ} (k : Fin n) (hk : k.val + 1 = n) :
    leafExtension (CartanMatrix.A n) k (-1) (-2) = CartanMatrix.C (n + 1) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [leafExtension, CartanMatrix.A, CartanMatrix.C, Fin.ext_iff] <;> grind

theorem leafExtension_A_penultimate_eq_D {n : ℕ} (hn : 3 ≤ n)
    (k : Fin n) (hk : k.val + 2 = n) :
    leafExtension (CartanMatrix.A n) k (-1) (-1) = CartanMatrix.D (n + 1) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [leafExtension, CartanMatrix.A, CartanMatrix.D, Fin.ext_iff] <;> grind

theorem leafExtension_B_first_numbering {n : ℕ} (hn : 2 ≤ n)
    (k : Fin n) (hk : k.val = 0) :
    ∀ i j, leafExtension (CartanMatrix.B n) k (-1) (-1) i j =
      CartanMatrix.B (n + 1) (finRotate (n + 1) i) (finRotate (n + 1) j) := by
  intro i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [leafExtension, CartanMatrix.B, Fin.ext_iff] <;> grind

theorem leafExtension_C_first_numbering {n : ℕ} (hn : 2 ≤ n)
    (k : Fin n) (hk : k.val = 0) :
    ∀ i j, leafExtension (CartanMatrix.C n) k (-1) (-1) i j =
      CartanMatrix.C (n + 1) (finRotate (n + 1) i) (finRotate (n + 1) j) := by
  intro i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [leafExtension, CartanMatrix.C, Fin.ext_iff] <;> grind

theorem leafExtension_D_first_numbering {n : ℕ} (hn : 4 ≤ n)
    (k : Fin n) (hk : k.val = 0) :
    ∀ i j, leafExtension (CartanMatrix.D n) k (-1) (-1) i j =
      CartanMatrix.D (n + 1) (finRotate (n + 1) i) (finRotate (n + 1) j) := by
  intro i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [leafExtension, CartanMatrix.D, Fin.ext_iff] <;> grind

end Langlands.LinearAlgebra.FiniteCartanMatrix
