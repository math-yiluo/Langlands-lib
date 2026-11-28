import Langlands.Algebra.BinaryElementaryQuotient
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Commutator.Basic

/-! # Elementary binary matrices: commutators, determinant one and list products -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.BinaryElementary

universe u v

section Ring

variable {R : Type u} [Ring R]

/-- The embedding `g ↦ diag(g, 1)` of coefficient units into binary matrix units. -/
def diagonalLeft : Rˣ →* GL₂ R where
  toFun g := diagonal g 1
  map_one' := diagonal_one
  map_mul' g h := by rw [diagonal_mul, mul_one]

@[simp] theorem diagonalLeft_apply (g : Rˣ) : diagonalLeft g = diagonal g 1 := rfl

/-- `diag([a, b], 1)` is elementary. -/
theorem diagonal_commutator_mem (a b : Rˣ) :
    diagonal (a * b * a⁻¹ * b⁻¹) 1 ∈ elementary R := by
  have h : diagonal (a * b * a⁻¹ * b⁻¹) 1 =
      diagonal a a⁻¹ * diagonal b b⁻¹ * diagonal (b * a)⁻¹ (b * a)⁻¹⁻¹ := by
    rw [diagonal_mul, diagonal_mul, inv_inv]
    congr 1 <;> group
  rw [h]
  exact (elementary R).mul_mem ((elementary R).mul_mem (diagonal_inverse_mem a)
    (diagonal_inverse_mem b)) (diagonal_inverse_mem _)

/-- Every element of the commutator subgroup of the coefficient units gives an elementary
`diag(g, 1)`. -/
theorem diagonal_mem_of_mem_commutator {g : Rˣ} (hg : g ∈ commutator Rˣ) :
    diagonal g 1 ∈ elementary R := by
  have hle : commutator Rˣ ≤ (elementary R).comap diagonalLeft := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    simpa [commutatorElement_def] using diagonal_commutator_mem a b
  exact hle hg

/-! ### Lists of elementary blocks -/

/-- The product of the blocks `upper p * lower q` along a list of pairs. -/
def listProd (l : List (R × R)) : GL₂ R :=
  (l.map fun pq => upper pq.1 * lower pq.2).prod

@[simp] theorem listProd_nil : listProd ([] : List (R × R)) = 1 := rfl

theorem listProd_cons (pq : R × R) (l : List (R × R)) :
    listProd (pq :: l) = upper pq.1 * lower pq.2 * listProd l := by
  simp [listProd]

theorem listProd_append (l l' : List (R × R)) :
    listProd (l ++ l') = listProd l * listProd l' := by
  simp [listProd, List.map_append, List.prod_append]

theorem listProd_replicate_zero (k : ℕ) :
    listProd (List.replicate k ((0 : R), (0 : R))) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, listProd_cons, ih]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem listProd_mem (l : List (R × R)) : listProd l ∈ elementary R := by
  induction l with
  | nil => exact (elementary R).one_mem
  | cons pq l ih =>
    rw [listProd_cons]
    exact (elementary R).mul_mem ((elementary R).mul_mem (upper_mem _) (lower_mem _)) ih

/-- The inverse of a list product is a list product. -/
theorem listProd_inv (l : List (R × R)) :
    (listProd l)⁻¹ =
      listProd (l.reverse.map fun pq => [((0 : R), -pq.2), (-pq.1, (0 : R))]).flatten := by
  induction l with
  | nil => simp
  | cons pq l ih =>
    rw [listProd_cons, mul_inv_rev, ih, List.reverse_cons, List.map_append,
      List.flatten_append, listProd_append]
    congr 1
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [listProd, Matrix.mul_apply, Fin.sum_univ_two]

/-- Every elementary binary matrix is a list product of elementary blocks. -/
theorem exists_listProd_of_mem {g : GL₂ R} (hg : g ∈ elementary R) :
    ∃ l : List (R × R), g = listProd l := by
  refine Subgroup.closure_induction (fun x hx => ?_) ⟨[], rfl⟩
    (fun x y _ _ ⟨l, hl⟩ ⟨l', hl'⟩ => ⟨l ++ l', by rw [listProd_append, hl, hl']⟩)
    (fun x _ ih => by obtain ⟨l, rfl⟩ := ih; exact ⟨_, listProd_inv l⟩) hg
  rcases hx with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · refine ⟨[(p, 0)], ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [listProd]
  · refine ⟨[(0, q)], ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [listProd]

/-- Padding a list product by trivial blocks does not change it. -/
theorem listProd_pad (l : List (R × R)) (k : ℕ) :
    listProd (l ++ List.replicate k (0, 0)) = listProd l := by
  rw [listProd_append, listProd_replicate_zero, mul_one]

/-- A ring homomorphism carries list products to list products. -/
theorem map_listProd {S : Type v} [Ring S] (f : R →+* S) (l : List (R × R)) :
    ((listProd l : GL₂ R) : Matrix (Fin 2) (Fin 2) R).map f =
      (listProd (l.map fun pq => (f pq.1, f pq.2)) : GL₂ S) := by
  induction l with
  | nil => simp [listProd, Matrix.map_one]
  | cons pq l ih =>
    rw [List.map_cons, listProd_cons, listProd_cons, Units.val_mul, Units.val_mul,
      Matrix.map_mul, ih, Units.val_mul, Units.val_mul, Matrix.map_mul]
    congr 2
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp

end Ring

/-! ### Determinant-one matrices over fields with `2 ≠ 0` lie in the commutator subgroup -/

section Field

variable {L : Type u} [Field L] {n : Type v} [Fintype n] [DecidableEq n]

open Matrix
open scoped commutatorElement

/-- The unit given by a transvection. -/
def transvectionUnit {i j : n} (hij : i ≠ j) (c : L) : (Matrix n n L)ˣ where
  val := transvection i j c
  inv := transvection i j (-c)
  val_inv := by
    rw [Matrix.transvection_mul_transvection_same i j hij c (-c), add_neg_cancel,
      Matrix.transvection_zero]
  inv_val := by
    rw [Matrix.transvection_mul_transvection_same i j hij (-c) c, neg_add_cancel,
      Matrix.transvection_zero]

/-- The unit given by a diagonal matrix with unit entries. -/
def diagonalUnit : (n → Lˣ) →* (Matrix n n L)ˣ where
  toFun f :=
    { val := diagonal fun k => (f k : L)
      inv := diagonal fun k => ((f k)⁻¹ : Lˣ)
      val_inv := by rw [diagonal_mul_diagonal]; simp
      inv_val := by rw [diagonal_mul_diagonal]; simp }
  map_one' := by ext : 1; simp
  map_mul' f g := by ext : 1; simp [diagonal_mul_diagonal]

@[simp] theorem diagonalUnit_val (f : n → Lˣ) :
    ((diagonalUnit f : (Matrix n n L)ˣ) : Matrix n n L) = Matrix.diagonal fun k => (f k : L) :=
  rfl

/-- A transvection is a commutator of invertible matrices when `2 ≠ 0`. -/
theorem transvectionUnit_mem_commutator (h2 : (2 : L) ≠ 0) {i j : n} (hij : i ≠ j) (c : L) :
    transvectionUnit hij c ∈ commutator (Matrix n n L)ˣ := by
  let d : n → Lˣ := Function.update 1 i (Units.mk0 2 h2)
  have hconj : ((diagonalUnit d * transvectionUnit hij c * (diagonalUnit d)⁻¹ :
      (Matrix n n L)ˣ) : Matrix n n L) = transvection i j (2 * c) := by
    ext a b
    simp only [Units.val_mul, Units.inv_mk, diagonalUnit, MonoidHom.coe_mk, OneHom.coe_mk,
      Units.val_inv_eq_inv_val]
    change (Matrix.diagonal (fun k => (d k : L)) * transvection i j c *
      Matrix.diagonal fun k => ((d k : L))⁻¹) a b = _
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hdi : (d i : L) = 2 := by simp [d]
    have hdk : ∀ k, k ≠ i → (d k : L) = 1 := fun k hk => by simp [d, Function.update_of_ne hk]
    have hinv : ∀ k, (d k : L) * (d k : L)⁻¹ = 1 := fun k => mul_inv_cancel₀ (d k).ne_zero
    simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    by_cases hab : a = b
    · subst hab
      have : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
      simp only [↓reduceIte, this, add_zero, mul_one, hinv]
    · by_cases hai : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := hai
        simp only [hab, ↓reduceIte, and_self, zero_add, hdi, hdk j (Ne.symm hij), inv_one,
          mul_one]
      · simp [hab, hai]

  have hcomm : ⁅diagonalUnit d, transvectionUnit hij c⁆ = transvectionUnit hij c := by
    apply Units.ext
    rw [commutatorElement_def, Units.val_mul, hconj]
    change transvection i j (2 * c) * transvection i j (-c) = transvection i j c
    rw [Matrix.transvection_mul_transvection_same i j hij]
    congr 1
    ring
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- Conjugating a diagonal matrix by the permutation matrix of a transposition permutes its
entries. -/
theorem swap_mul_diagonal_mul_swap (i k : n) (f : n → L) :
    (Equiv.swap i k).permMatrix L * Matrix.diagonal f * (Equiv.swap i k).permMatrix L =
      Matrix.diagonal (f ∘ Equiv.swap i k) := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext a b
  simp only [Matrix.submatrix_apply, id, Matrix.diagonal_apply, Function.comp_apply,
    Equiv.symm_swap]
  by_cases hab : a = b
  · subst hab; simp
  · have : Equiv.swap i k a ≠ Equiv.swap i k b := fun h => hab ((Equiv.swap i k).injective h)
    simp [hab, this]

/-- The permutation matrix of a transposition, as a unit. -/
def swapUnit (i k : n) : (Matrix n n L)ˣ where
  val := (Equiv.swap i k).permMatrix L
  inv := (Equiv.swap i k).permMatrix L
  val_inv := by rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]
  inv_val := by rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]

/-- `diag(…, c, …, c⁻¹, …)` is a commutator. -/
theorem diagonalUnit_pair_mem_commutator {i k : n} (hik : i ≠ k) (c : Lˣ) :
    diagonalUnit (Function.update (Function.update 1 i c) k c⁻¹) ∈ commutator (Matrix n n L)ˣ := by
  have h : ⁅diagonalUnit (Function.update 1 i c), swapUnit (L := L) i k⁆ =
      diagonalUnit (Function.update (Function.update 1 i c) k c⁻¹) := by
    apply Units.ext
    rw [commutatorElement_def, ← map_inv]
    have e1 : ((swapUnit (L := L) i k)⁻¹ : (Matrix n n L)ˣ).val =
        (Equiv.swap i k).permMatrix L := rfl
    simp only [Units.val_mul, e1, diagonalUnit_val]
    change Matrix.diagonal _ * (Equiv.swap i k).permMatrix L * Matrix.diagonal _ *
      (Equiv.swap i k).permMatrix L = _
    rw [mul_assoc (Matrix.diagonal _), mul_assoc (Matrix.diagonal _),
      swap_mul_diagonal_mul_swap, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    simp only [Function.comp_apply, Pi.inv_apply, Function.update_apply, Equiv.swap_apply_def,
      Pi.one_apply]
    by_cases hak : a = k
    · subst hak; simp [Ne.symm hik]
    · by_cases hai : a = i
      · subst hai; simp [hik, Ne.symm hik]
      · simp [hai, hak]
  rw [← h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- A diagonal matrix of determinant one is a product of commutators. -/
theorem diagonalUnit_mem_commutator (f : n → Lˣ) (hf : ∏ i, f i = 1) :
    diagonalUnit f ∈ commutator (Matrix n n L)ˣ := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · have : f = 1 := funext fun i => isEmptyElim i
    rw [this, map_one]
    exact (commutator _).one_mem
  let H : Subgroup (n → Lˣ) := (commutator (Matrix n n L)ˣ).comap diagonalUnit
  let g : n → (n → Lˣ) := fun i => Function.update (Function.update 1 i (f i)) i₀ (f i)⁻¹
  have hg : ∀ i ∈ Finset.univ.erase i₀, g i ∈ H := fun i hi =>
    diagonalUnit_pair_mem_commutator (Finset.ne_of_mem_erase hi) (f i)
  have hprod : ∏ i ∈ Finset.univ.erase i₀, g i = f := by
    funext k
    rw [Finset.prod_apply]
    by_cases hk : k = i₀
    · subst hk
      simp only [g, Function.update_self]
      rw [Finset.prod_inv_distrib, inv_eq_iff_eq_inv, eq_inv_iff_mul_eq_one, mul_comm]
      rwa [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ k)] at hf
    · simp only [g, Function.update_of_ne hk]
      rw [Finset.prod_eq_single k]
      · simp
      · intro b _ hb
        simp [Function.update_of_ne (Ne.symm hb)]
      · intro hk'
        exact absurd (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) hk'
  have : f ∈ H := hprod ▸ Subgroup.prod_mem H hg
  exact this

/-- Every matrix of determinant one over a field with `2 ≠ 0` lies in the commutator subgroup
of the invertible matrices. -/
theorem mem_commutator_of_det_eq_one (h2 : (2 : L) ≠ 0) (g : (Matrix n n L)ˣ)
    (hg : (g : Matrix n n L).det = 1) : g ∈ commutator (Matrix n n L)ˣ := by
  let P : Matrix n n L → Prop := fun M => ∃ h ∈ commutator (Matrix n n L)ˣ,
    (h : Matrix n n L) = M
  have hP : P g := by
    refine Matrix.diagonal_transvection_induction P (g : Matrix n n L) ?_ ?_ ?_
    · intro D hD
      rw [hg, Matrix.det_diagonal] at hD
      have hD0 : ∀ i, D i ≠ 0 := fun i h0 => by
        rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at hD
        exact zero_ne_one hD
      let f : n → Lˣ := fun i => Units.mk0 (D i) (hD0 i)
      refine ⟨diagonalUnit f, diagonalUnit_mem_commutator f ?_, rfl⟩
      apply Units.ext
      simpa [f] using hD
    · intro t
      exact ⟨transvectionUnit t.hij t.c, transvectionUnit_mem_commutator h2 t.hij t.c, rfl⟩
    · rintro A B ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a * b, (commutator _).mul_mem ha hb, rfl⟩
  obtain ⟨h, hh, hhg⟩ := hP
  rwa [Units.ext hhg] at hh

end Field

end Langlands.CentralSimple.Landherr
