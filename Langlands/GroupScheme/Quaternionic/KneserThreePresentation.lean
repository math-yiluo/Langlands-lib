import Langlands.GroupScheme.Examples.SU3RootParameters
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Quaternion-type rings presented over a commutative ring with involution

A `Presentation A B` writes a ring `B` as `B = ι(A) ⊕ j ι(A)` over a commutative ring `A` with
involution `a ↦ ā`, where `j ι(a) = ι(ā) j` and `j² = ι(δ)`. For a quaternion algebra `D`
containing a quadratic subfield `L`, and a commutative coefficient ring `R`, the ring
`R ⊗ D` is presented over `L ⊗ R` in this way.

`rep b` is the `2 × 2` matrix `[[a, δ c̄], [c, ā]]` of left multiplication by `b = ι a + j ι c`
in the right `A`-basis `(1, j)`. It is an injective ring homomorphism, and `block` applies it
entrywise to square matrices.
-/

namespace Langlands.GroupScheme.KneserThree

open SU3Root

/-- A presentation `B = ι(A) ⊕ j ι(A)`. -/
structure Presentation (A : Type*) [CommRing A] (B : Type*) [Ring B] where
  c : RingInvolution A
  ι : A →+* B
  j : B
  δ : A
  bar_δ : c.bar δ = δ
  j_mul : ∀ a, j * ι a = ι (c.bar a) * j
  j_mul_self : j * j = ι δ
  fst : B →+ A
  snd : B →+ A
  decompose : ∀ b, ι (fst b) + j * ι (snd b) = b
  fst_mk : ∀ a a', fst (ι a + j * ι a') = a
  snd_mk : ∀ a a', snd (ι a + j * ι a') = a'

namespace Presentation

variable {A B : Type*} [CommRing A] [Ring B] (P : Presentation A B)

/-- The element `ι a + j ι a'`. -/
def elem (a a' : A) : B := P.ι a + P.j * P.ι a'

@[simp] theorem fst_elem (a a' : A) : P.fst (P.elem a a') = a := P.fst_mk a a'

@[simp] theorem snd_elem (a a' : A) : P.snd (P.elem a a') = a' := P.snd_mk a a'

theorem elem_fst_snd (b : B) : P.elem (P.fst b) (P.snd b) = b := P.decompose b

theorem ext {b b' : B} (h₁ : P.fst b = P.fst b') (h₂ : P.snd b = P.snd b') : b = b' := by
  rw [← P.elem_fst_snd b, ← P.elem_fst_snd b', h₁, h₂]

theorem ι_mul_j (a : A) : P.ι a * P.j = P.j * P.ι (P.c.bar a) := by
  rw [P.j_mul, RingInvolution.bar_bar]

theorem elem_mul (a a' e e' : A) :
    P.elem a a' * P.elem e e' =
      P.elem (a * e + P.δ * P.c.bar a' * e') (P.c.bar a * e' + a' * e) := by
  simp only [elem, add_mul, mul_add, map_add, map_mul]
  have h1 : P.ι a * (P.j * P.ι e') = P.j * (P.ι (P.c.bar a) * P.ι e') := by
    rw [← mul_assoc, P.ι_mul_j, mul_assoc]
  have h2 : P.j * P.ι a' * P.ι e = P.j * (P.ι a' * P.ι e) := mul_assoc _ _ _
  have h3 : P.j * P.ι a' * (P.j * P.ι e') =
      P.ι P.δ * P.ι (P.c.bar a') * P.ι e' := by
    rw [mul_assoc, ← mul_assoc (P.ι a'), P.ι_mul_j, ← mul_assoc, ← mul_assoc,
      P.j_mul_self, mul_assoc]
  rw [h1, h2, h3]
  noncomm_ring

@[simp] theorem fst_mul (b b' : B) :
    P.fst (b * b') = P.fst b * P.fst b' + P.δ * P.c.bar (P.snd b) * P.snd b' := by
  conv_lhs => rw [← P.elem_fst_snd b, ← P.elem_fst_snd b', elem_mul]
  exact P.fst_elem _ _

@[simp] theorem snd_mul (b b' : B) :
    P.snd (b * b') = P.c.bar (P.fst b) * P.snd b' + P.snd b * P.fst b' := by
  conv_lhs => rw [← P.elem_fst_snd b, ← P.elem_fst_snd b', elem_mul]
  exact P.snd_elem _ _

theorem elem_one : P.elem 1 0 = 1 := by simp [elem]

@[simp] theorem fst_one : P.fst 1 = 1 := by rw [← P.elem_one, fst_elem]

@[simp] theorem snd_one : P.snd 1 = 0 := by rw [← P.elem_one, snd_elem]

@[simp] theorem fst_ι (a : A) : P.fst (P.ι a) = a := by
  have : P.ι a = P.elem a 0 := by simp [elem]
  rw [this, fst_elem]

@[simp] theorem snd_ι (a : A) : P.snd (P.ι a) = 0 := by
  have : P.ι a = P.elem a 0 := by simp [elem]
  rw [this, snd_elem]

@[simp] theorem fst_j : P.fst P.j = 0 := by
  have : P.j = P.elem 0 1 := by simp [elem]
  rw [this, fst_elem]

@[simp] theorem snd_j : P.snd P.j = 1 := by
  have : P.j = P.elem 0 1 := by simp [elem]
  rw [this, snd_elem]

/-- The matrix `[[a, δ c̄], [c, ā]]` of left multiplication by `b = ι a + j ι c`. -/
def rep (b : B) : Matrix (Fin 2) (Fin 2) A :=
  !![P.fst b, P.δ * P.c.bar (P.snd b); P.snd b, P.c.bar (P.fst b)]

theorem rep_mul (b b' : B) : P.rep (b * b') = P.rep b * P.rep b' := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [rep, Matrix.mul_apply, Fin.sum_univ_two, P.bar_δ] <;> ring

theorem rep_add (b b' : B) : P.rep (b + b') = P.rep b + P.rep b' := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [rep] <;> ring

theorem rep_zero : P.rep 0 = 0 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [rep]

theorem rep_one : P.rep 1 = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [rep]

theorem rep_injective : Function.Injective P.rep := by
  intro b b' h
  apply P.ext
  · simpa [rep] using congrFun (congrFun h 0) 0
  · simpa [rep] using congrFun (congrFun h 1) 0

/-- The conjugation `ι a + j ι c ↦ ι ā - j ι c`. -/
def bar (b : B) : B := P.elem (P.c.bar (P.fst b)) (-P.snd b)

@[simp] theorem fst_bar (b : B) : P.fst (P.bar b) = P.c.bar (P.fst b) := P.fst_elem _ _

@[simp] theorem snd_bar (b : B) : P.snd (P.bar b) = -P.snd b := P.snd_elem _ _

/-- The standard symplectic matrix `[[0, 1], [-1, 0]]`. -/
def symplectic : Matrix (Fin 2) (Fin 2) A := !![0, 1; -1, 0]

theorem rep_bar_mul_symplectic (b : B) :
    P.rep (P.bar b) * symplectic = symplectic * (P.rep b).transpose := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [rep, symplectic, Matrix.mul_apply, Fin.sum_univ_two]

variable {n : Type*}

/-- Entrywise `rep`: the matrix of a `B`-linear map of `B^n` over `A`. -/
def block (X : Matrix n n B) : Matrix (n × Fin 2) (n × Fin 2) A :=
  Matrix.of fun p q => P.rep (X p.1 q.1) p.2 q.2

theorem block_apply (X : Matrix n n B) (p q : n × Fin 2) :
    P.block X p q = P.rep (X p.1 q.1) p.2 q.2 := rfl

theorem rep_sum (s : Finset n) (f : n → B) :
    P.rep (∑ i ∈ s, f i) = ∑ i ∈ s, P.rep (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rep_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rep_add, ih]

variable [Fintype n] [DecidableEq n]

theorem block_mul (X Y : Matrix n n B) : P.block (X * Y) = P.block X * P.block Y := by
  ext ⟨i, a⟩ ⟨k, b⟩
  simp only [block_apply, Matrix.mul_apply, rep_sum, rep_mul, Fintype.sum_prod_type]
  rw [Matrix.sum_apply]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem block_one : P.block (1 : Matrix n n B) = 1 := by
  ext ⟨i, a⟩ ⟨k, b⟩
  by_cases h : i = k
  · subst h
    simp [block_apply, Matrix.one_apply, rep_one]
  · simp [block_apply, h, rep_zero]

theorem block_injective : Function.Injective (P.block (n := n)) := by
  intro X Y h
  ext i k
  apply P.rep_injective
  ext a b
  exact congrFun (congrFun h (i, a)) (k, b)

/-- The conjugate transpose `(X^*)_{ik} = bar (X_{ki})`. -/
def conjTranspose (X : Matrix n n B) : Matrix n n B := Matrix.of fun i k => P.bar (X k i)

/-- The block-diagonal symplectic matrix. -/
def blockSymplectic : Matrix (n × Fin 2) (n × Fin 2) A :=
  Matrix.of fun p q => if p.1 = q.1 then symplectic p.2 q.2 else 0

theorem block_conjTranspose_mul (X : Matrix n n B) :
    P.block (P.conjTranspose X) * blockSymplectic =
      blockSymplectic * (P.block X).transpose := by
  ext ⟨i, a⟩ ⟨k, b⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, blockSymplectic, block_apply,
    conjTranspose, Matrix.of_apply, Matrix.transpose_apply]
  have h := congrFun (congrFun (P.rep_bar_mul_symplectic (X k i)) a) b
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at h
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Fin.sum_univ_two, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact h

theorem blockSymplectic_mul_self :
    (blockSymplectic : Matrix (n × Fin 2) (n × Fin 2) A) * blockSymplectic = -1 := by
  ext ⟨i, a⟩ ⟨k, b⟩
  by_cases h : i = k
  · subst h
    fin_cases a <;> fin_cases b <;>
      simp [blockSymplectic, symplectic, Matrix.mul_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Matrix.one_apply]
  · simp [blockSymplectic, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, h]

end Presentation

end Langlands.GroupScheme.KneserThree
