import Langlands.Representation.RankinSelberg.FiniteCauchyBinet
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Instances.Matrix

/-! # Matrix action on families of subsets -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.CompoundMinorProduct

open Finset Matrix

variable {ι α R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder α] [DecidableEq α] [Fintype α]
  [CommRing R]

/-- The indices for a product of compound matrices with prescribed minor degrees. -/
abbrev Selection (α : Type*) (degree : ι → ℕ) :=
  (t : ι) → {s : Finset α // s.card = degree t}

variable {degree : ι → ℕ}

/-- A minor with both sets of indices in increasing order. -/
def minor {d : ℕ} (A : Matrix α α R) (s t : {s : Finset α // s.card = d}) : R :=
  (A.submatrix (s.val.orderEmbOfFin s.property) (t.val.orderEmbOfFin t.property)).det

omit [Fintype α] in
theorem minor_diagonal {d : ℕ} (a : α → R) (s t : {s : Finset α // s.card = d}) :
    minor (diagonal a) s t = if s = t then ∏ i ∈ s.val, a i else 0 := by
  split_ifs with h
  · subst t
    rw [minor, submatrix_diagonal _ _ (s.val.orderEmbOfFin s.property).injective, det_diagonal]
    calc
      _ = ∏ i ∈ univ.map (s.val.orderEmbOfFin s.property).toEmbedding, a i :=
        (prod_map _ _ _).symm
      _ = ∏ i ∈ s.val, a i := by rw [map_orderEmbOfFin_univ]
  · have hn : ¬ s.val ⊆ t.val := fun hst =>
      h (Subtype.ext (eq_of_subset_of_card_le hst (t.property.trans s.property.symm).le))
    obtain ⟨x, hxs, hxt⟩ := not_subset.mp hn
    have hx : x ∈ Set.range (s.val.orderEmbOfFin s.property) := by simpa using hxs
    obtain ⟨i, rfl⟩ := hx
    apply det_eq_zero_of_row_eq_zero i
    intro j
    apply diagonal_apply_ne
    intro h
    exact hxt (h ▸ orderEmbOfFin_mem t.val t.property j)

theorem minor_mul {d : ℕ} (A B : Matrix α α R) (s t : {s : Finset α // s.card = d}) :
    minor (A * B) s t = ∑ u : {u : Finset α // u.card = d}, minor A s u * minor B u t := by
  have h : (A * B).submatrix (s.val.orderEmbOfFin s.property) (t.val.orderEmbOfFin t.property) =
      A.submatrix (s.val.orderEmbOfFin s.property) id *
        B.submatrix id (t.val.orderEmbOfFin t.property) := rfl
  rw [minor, h, Langlands.GeneralLinear.Spherical.det_rectangular_mul]
  rfl

/-- The matrix whose entries are products of the corresponding ordered minors. -/
def matrix (degree : ι → ℕ) (A : Matrix α α R) :
    Matrix (Selection α degree) (Selection α degree) R :=
  fun q r => ∏ t, minor A (q t) (r t)

omit [DecidableEq ι] [Fintype α] in
theorem matrix_diagonal (a : α → R) :
    matrix degree (diagonal a) = diagonal fun q => ∏ t, ∏ i ∈ (q t).val, a i := by
  ext q r
  rw [diagonal_apply]
  change (∏ t, minor (diagonal a) (q t) (r t)) = _
  split_ifs with h
  · subst r
    simp [minor_diagonal]
  · have hne : ∃ t, q t ≠ r t := by
      by_contra! heq
      exact h (funext heq)
    obtain ⟨t, ht⟩ := hne
    apply prod_eq_zero (mem_univ t)
    simp [minor_diagonal, ht]

/-- Cauchy–Binet makes the product of compounds multiplicative. -/
def matrixHom (degree : ι → ℕ) :
    Matrix α α R →* Matrix (Selection α degree) (Selection α degree) R where
  toFun := matrix degree
  map_one' := by
    rw [← diagonal_one, matrix_diagonal]
    simp
  map_mul' A B := by
    ext q r
    simp only [matrix, minor_mul, Matrix.mul_apply]
    rw [Fintype.prod_sum]
    exact sum_congr rfl fun u _ => prod_mul_distrib

/-- The compound matrix acts on the functions on configurations by multiplication of columns. -/
def action (degree : ι → ℕ) :
    Matrix α α R →* Module.End R (Selection α degree → R) :=
  Matrix.toLinAlgEquiv'.toAlgHom.toMonoidHom.comp (matrixHom degree)

theorem action_apply (A : Matrix α α R) (x : Selection α degree → R) :
    action degree A x = matrix degree A *ᵥ x :=
  rfl

theorem action_single (A : Matrix α α R) (r : Selection α degree) (q : Selection α degree) :
    action degree A (Pi.single r 1) q = matrix degree A q r := by
  rw [action_apply, Matrix.mulVec_single_one, Matrix.col_apply]

theorem action_diagonal (a : α → R) (q : Selection α degree) :
    action degree (diagonal a) (Pi.single q 1) =
      (∏ t, ∏ i ∈ (q t).val, a i) • Pi.single q 1 := by
  ext r
  rw [action_single, matrix_diagonal, Matrix.diagonal_apply]
  by_cases h : r = q
  · subst r
    simp
  · simp [h]

omit [Fintype ι] [DecidableEq ι] [Fintype α] [CommRing R] in
/-- Apply a row permutation to every subset in a configuration. -/
def reindex (e : Equiv.Perm α) : Equiv.Perm (Selection α degree) where
  toFun q t := ⟨(q t).val.map e.toEmbedding, (card_map _).trans (q t).property⟩
  invFun q t := ⟨(q t).val.map e.symm.toEmbedding, (card_map _).trans (q t).property⟩
  left_inv q := funext fun t => Subtype.ext (by
    ext a
    simp [Finset.mem_map_equiv])
  right_inv q := funext fun t => Subtype.ext (by
    ext a
    simp [Finset.mem_map_equiv])

omit [Fintype ι] [DecidableEq ι] [LinearOrder α] [DecidableEq α] [Fintype α] [CommRing R] in
theorem reindex_symm (e : Equiv.Perm α) :
    (reindex (degree := degree) e).symm = reindex e.symm :=
  rfl

omit [DecidableEq ι] in
private theorem minor_perm_eq_zero (e : Equiv.Perm α) {d : ℕ}
    (q r : {s : Finset α // s.card = d}) (h : q.val ≠ r.val.map e.toEmbedding) :
    minor (Matrix.permMatrixHom (R := R) e) q r = 0 := by
  have hn : ¬ q.val ⊆ r.val.map e.toEmbedding := fun hsub =>
    h (eq_of_subset_of_card_le hsub (by rw [card_map, q.property, r.property]))
  obtain ⟨a, haq, har⟩ := not_subset.mp hn
  have ha : a ∈ Set.range (q.val.orderEmbOfFin q.property) := by simpa using haq
  obtain ⟨i, rfl⟩ := ha
  apply det_eq_zero_of_row_eq_zero i
  intro j
  have hj : e.symm (q.val.orderEmbOfFin q.property i) ≠ r.val.orderEmbOfFin r.property j := by
    intro hEq
    apply har
    rw [mem_map_equiv, hEq]
    exact orderEmbOfFin_mem _ _ _
  simp [Matrix.permMatrixHom, Equiv.Perm.inv_def, Matrix.submatrix_apply,
    Equiv.toPEquiv_apply, hj]

omit [DecidableEq ι] in
theorem matrix_perm_eq_zero (e : Equiv.Perm α) (q r : Selection α degree)
    (h : q ≠ reindex e r) : matrix degree (Matrix.permMatrixHom (R := R) e) q r = 0 := by
  have hne : ∃ t, (q t).val ≠ (r t).val.map e.toEmbedding := by
    by_contra! heq
    exact h (funext fun t => Subtype.ext (heq t))
  obtain ⟨t, ht⟩ := hne
  exact prod_eq_zero (mem_univ t) (minor_perm_eq_zero e (q t) (r t) ht)

theorem action_perm_single (e : Equiv.Perm α) (r : Selection α degree) :
    action degree (Matrix.permMatrixHom (R := R) e) (Pi.single r 1) =
      matrix degree (Matrix.permMatrixHom (R := R) e) (reindex e r) r •
        Pi.single (reindex e r) 1 := by
  ext q
  rw [action_single]
  by_cases h : q = reindex e r
  · subst q
    simp
  · rw [matrix_perm_eq_zero e q r h]
    simp [Pi.single_eq_of_ne h]

/-- An invertible row permutation carries a basis vector to a nonzero multiple of the
permuted basis vector. -/
theorem exists_action_perm_single [Nontrivial R] (e : Equiv.Perm α) (r : Selection α degree) :
    ∃ c : R, c ≠ 0 ∧ action degree (Matrix.permMatrixHom (R := R) e) (Pi.single r 1) =
      c • Pi.single (reindex e r) 1 := by
  refine ⟨_, ?_, action_perm_single e r⟩
  intro hz
  have hinv : action degree (Matrix.permMatrixHom (R := R) e⁻¹)
      (action degree (Matrix.permMatrixHom (R := R) e) (Pi.single r 1)) = Pi.single r 1 := by
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
      Module.End.one_apply]
  rw [action_perm_single, hz, zero_smul, map_zero] at hinv
  exact (zero_ne_one : (0 : R) ≠ 1) (by simpa using congrFun hinv r)

section Continuity

variable {X : Type*} [TopologicalSpace X] [TopologicalSpace R] [IsTopologicalRing R]

omit [DecidableEq ι] [DecidableEq α] [Fintype α] in
theorem continuous_matrix {A : X → Matrix α α R} (hA : Continuous A) :
    Continuous fun x => matrix degree (A x) := by
  apply _root_.continuous_matrix
  intro q r
  exact continuous_finsetProd _ (fun t _ => (hA.matrix_submatrix _ _).matrix_det)

theorem continuous_action {A : X → Matrix α α R} (hA : Continuous A) (x : Selection α degree → R) :
    Continuous fun a => action degree (A a) x :=
  (continuous_matrix hA).matrix_mulVec continuous_const

end Continuity

variable {S : Type*} [CommRing S]

omit [DecidableEq ι] [DecidableEq α] [Fintype α] in
theorem map_matrix (f : R →+* S) (A : Matrix α α R) :
    (matrix degree A).map f = matrix degree (A.map f) := by
  ext q r
  simp [matrix, minor, map_prod, f.map_det]
  rfl

end Langlands.Archimedean.CompoundMinorProduct
