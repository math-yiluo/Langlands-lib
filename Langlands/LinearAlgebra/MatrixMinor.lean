import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Topology.Instances.Matrix
import Langlands.Representation.RankinSelberg.FiniteCauchyBinet

/-!
# Minors of square matrices

For a square matrix `X : Matrix (Fin n) (Fin n) R` over a commutative ring and finite sets
`A B : Finset (Fin n)` of rows and columns, `minor X A B` is the determinant of the submatrix
with rows `A` and columns `B`, both listed in increasing order. It is `0` if `A` and `B` have
different cardinalities.

The module proves the Cauchy–Binet formula for minors of a product, the behaviour under
transposition, diagonal scaling, reindexing along order embeddings and ring homomorphisms,
minors of the identity matrix, of matrices with identity rows and of upper or lower triangular
matrices, continuity, and the
principal case of Jacobi's complementary minor theorem: if `X * Y = 1`, then
`det X * minor Y A A = minor X Aᶜ Aᶜ`. For an orthogonal matrix (`X * Xᵀ = 1`) this gives
`minor X A A = det X * minor X Aᶜ Aᶜ`.
-/

noncomputable section

open Finset
open scoped Matrix

namespace Langlands.Archimedean.MatrixMinor

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The minor of `X` with rows `A` and columns `B`, both enumerated in increasing order. It is
`0` when `A` and `B` have different cardinalities. -/
def minor (X : Matrix (Fin n) (Fin n) R) (A B : Finset (Fin n)) : R :=
  if h : A.card = B.card then
    (X.submatrix (A.orderEmbOfFin rfl) (B.orderEmbOfFin h.symm)).det
  else 0

/-! ## Basic properties -/

/-- The minor for sets of a common cardinality `k`, with explicit enumerations. -/
theorem minor_eq {X : Matrix (Fin n) (Fin n) R} {A B : Finset (Fin n)} {k : ℕ}
    (hA : A.card = k) (hB : B.card = k) :
    minor X A B = (X.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)).det := by
  subst hA
  rw [minor, dite_eq_left hB.symm]

theorem minor_of_card_ne {X : Matrix (Fin n) (Fin n) R} {A B : Finset (Fin n)}
    (h : A.card ≠ B.card) : minor X A B = 0 := by
  rw [minor, dite_eq_right h]

/-- The order enumeration of `Finset.univ`, as an equivalence. -/
def univEquiv (n : ℕ) : Fin (Finset.univ : Finset (Fin n)).card ≃ Fin n :=
  Equiv.ofBijective (Finset.univ.orderEmbOfFin rfl) ⟨(Finset.univ.orderEmbOfFin rfl).injective,
    fun j => by
      have hj : j ∈ Set.range (Finset.univ.orderEmbOfFin (rfl : (Finset.univ :
          Finset (Fin n)).card = _)) := by
        rw [range_orderEmbOfFin]
        exact Finset.mem_coe.mpr (Finset.mem_univ j)
      exact hj⟩

theorem minor_univ (X : Matrix (Fin n) (Fin n) R) : minor X univ univ = X.det := by
  rw [minor_eq rfl rfl]
  exact Matrix.det_submatrix_equiv_self (univEquiv n) X

theorem minor_empty (X : Matrix (Fin n) (Fin n) R) : minor X ∅ ∅ = 1 := by
  rw [minor_eq (k := 0) rfl rfl]
  exact Matrix.det_isEmpty

/-- Minors only depend on the entries in the selected rows and columns. -/
theorem minor_congr {X Y : Matrix (Fin n) (Fin n) R} {A B : Finset (Fin n)}
    (h : ∀ i ∈ A, ∀ j ∈ B, X i j = Y i j) : minor X A B = minor Y A B := by
  by_cases hc : A.card = B.card
  · rw [minor_eq rfl hc.symm, minor_eq rfl hc.symm]
    congr 1
    ext i j
    exact h _ (orderEmbOfFin_mem _ _ _) _ (orderEmbOfFin_mem _ _ _)
  · rw [minor_of_card_ne hc, minor_of_card_ne hc]

/-- A product over the increasing enumeration of a finite set is the product over the set. -/
theorem prod_orderEmbOfFin {M : Type*} [CommMonoid M] (s : Finset (Fin n)) {k : ℕ}
    (h : s.card = k) (f : Fin n → M) : ∏ i, f (s.orderEmbOfFin h i) = ∏ i ∈ s, f i := by
  conv_rhs => rw [← map_orderEmbOfFin_univ s h, prod_map]
  rfl

/-! ## Cauchy–Binet -/

/-- **Cauchy–Binet** for minors: a `k × k` minor of a product is the sum, over the `k`-element
sets `C` of indices, of the products of a minor of the first factor with columns `C` and a
minor of the second factor with rows `C`. -/
theorem minor_mul (X Y : Matrix (Fin n) (Fin n) R) {A B : Finset (Fin n)} {k : ℕ}
    (hA : A.card = k) (hB : B.card = k) :
    minor (X * Y) A B =
      ∑ C ∈ powersetCard k (univ : Finset (Fin n)), minor X A C * minor Y C B := by
  rw [minor_eq hA hB]
  have hsub : (X * Y).submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB) =
      X.submatrix (A.orderEmbOfFin hA) id * Y.submatrix id (B.orderEmbOfFin hB) :=
    Matrix.submatrix_mul X Y _ id _ Function.bijective_id
  rw [hsub, Langlands.GeneralLinear.Spherical.det_rectangular_mul,
    Finset.sum_subtype (p := fun C : Finset (Fin n) => C.card = k)
      (powersetCard k (univ : Finset (Fin n)))
      (fun C => by
        rw [mem_powersetCard]
        exact ⟨fun h => h.2, fun h => ⟨subset_univ _, h⟩⟩)
      (fun C => minor X A C * minor Y C B)]
  apply Finset.sum_congr rfl
  intro C _
  rw [minor_eq hA C.property, minor_eq C.property hB]
  rfl

/-! ## Transpose, diagonal scaling, identity -/

theorem minor_transpose (X : Matrix (Fin n) (Fin n) R) (A B : Finset (Fin n)) :
    minor Xᵀ A B = minor X B A := by
  by_cases hc : A.card = B.card
  · rw [minor_eq rfl hc.symm, minor_eq hc.symm rfl, ← Matrix.det_transpose]
    rfl
  · rw [minor_of_card_ne hc, minor_of_card_ne (Ne.symm hc)]

theorem minor_diagonal_mul (a : Fin n → R) (X : Matrix (Fin n) (Fin n) R)
    (A B : Finset (Fin n)) :
    minor (Matrix.diagonal a * X) A B = (∏ i ∈ A, a i) * minor X A B := by
  by_cases hc : A.card = B.card
  · rw [minor_eq rfl hc.symm, minor_eq rfl hc.symm]
    have hsub : (Matrix.diagonal a * X).submatrix (A.orderEmbOfFin rfl) (B.orderEmbOfFin hc.symm)
        = Matrix.diagonal (fun i => a (A.orderEmbOfFin rfl i)) *
          X.submatrix (A.orderEmbOfFin rfl) (B.orderEmbOfFin hc.symm) := by
      ext i j
      simp [Matrix.diagonal_mul]
    rw [hsub, Matrix.det_mul, Matrix.det_diagonal, prod_orderEmbOfFin]
  · rw [minor_of_card_ne hc, minor_of_card_ne hc, mul_zero]

theorem minor_mul_diagonal (X : Matrix (Fin n) (Fin n) R) (a : Fin n → R)
    (A B : Finset (Fin n)) :
    minor (X * Matrix.diagonal a) A B = minor X A B * ∏ j ∈ B, a j := by
  rw [← minor_transpose, Matrix.transpose_mul, Matrix.diagonal_transpose, minor_diagonal_mul,
    minor_transpose, mul_comm]

/-- Minors of the identity matrix. -/
theorem minor_one (A B : Finset (Fin n)) :
    minor (1 : Matrix (Fin n) (Fin n) R) A B = if A = B then 1 else 0 := by
  split_ifs with hAB
  · subst hAB
    rw [minor_eq rfl rfl, Matrix.submatrix_one _ (A.orderEmbOfFin rfl).injective, Matrix.det_one]
  · by_cases hc : A.card = B.card
    · have hnot : ¬ A ⊆ B := fun hs => hAB (eq_of_subset_of_card_le hs hc.symm.le)
      obtain ⟨a, haA, haB⟩ := not_subset.mp hnot
      have hr : a ∈ Set.range (A.orderEmbOfFin rfl) := by
        rw [range_orderEmbOfFin]
        exact haA
      obtain ⟨r, hr⟩ := hr
      rw [minor_eq rfl hc.symm]
      apply Matrix.det_eq_zero_of_row_eq_zero r
      intro j
      rw [Matrix.submatrix_apply, hr, Matrix.one_apply_ne]
      intro h
      exact haB (h ▸ orderEmbOfFin_mem _ _ _)
    · exact minor_of_card_ne hc

/-- Minors of a diagonal matrix. -/
theorem minor_diagonal (a : Fin n → R) (A B : Finset (Fin n)) :
    minor (Matrix.diagonal a) A B = if A = B then ∏ i ∈ A, a i else 0 := by
  rw [← mul_one (Matrix.diagonal a), minor_diagonal_mul, minor_one]
  split_ifs <;> simp

/-- If the rows of `X` with indices in `A` are those of the identity matrix, a minor with rows
`A` and columns `C`, `C` of the same cardinality, is `1` if `C = A` and `0` otherwise. -/
theorem minor_of_rows_eq_one {X : Matrix (Fin n) (Fin n) R} {A C : Finset (Fin n)}
    (h : ∀ i ∈ A, ∀ j, X i j = (1 : Matrix (Fin n) (Fin n) R) i j) :
    minor X A C = if C = A then 1 else 0 := by
  rw [minor_congr (Y := 1) fun i hi j _ => h i hi j, minor_one]
  exact if_congr eq_comm rfl rfl

/-! ## Triangular matrices -/

/-- Principal minors of an upper triangular matrix are products of diagonal entries. -/
theorem minor_of_isUpperTriangular {X : Matrix (Fin n) (Fin n) R} (h : X.IsUpperTriangular)
    (A : Finset (Fin n)) : minor X A A = ∏ i ∈ A, X i i := by
  rw [minor_eq rfl rfl]
  have ht : (X.submatrix (A.orderEmbOfFin rfl) (A.orderEmbOfFin rfl)).IsUpperTriangular :=
    fun i j hij => h ((A.orderEmbOfFin rfl).strictMono hij)
  rw [Matrix.det_of_isUpperTriangular ht]
  exact prod_orderEmbOfFin A rfl fun i => X i i

/-- Principal minors of a lower triangular matrix are products of diagonal entries. -/
theorem minor_of_isLowerTriangular {X : Matrix (Fin n) (Fin n) R} (h : X.IsLowerTriangular)
    (A : Finset (Fin n)) : minor X A A = ∏ i ∈ A, X i i := by
  rw [← minor_transpose]
  exact minor_of_isUpperTriangular (fun i j hij => h hij) A

/-! ## Reindexing along an order embedding -/

/-- The increasing enumeration of the image of `A` under an order embedding `e` is `e`
composed with the increasing enumeration of `A`. -/
theorem orderEmbOfFin_map {m : ℕ} (e : Fin m ↪o Fin n) (A : Finset (Fin m)) {k : ℕ}
    (h : A.card = k) (h' : (A.map e.toEmbedding).card = k) (i : Fin k) :
    (A.map e.toEmbedding).orderEmbOfFin h' i = e (A.orderEmbOfFin h i) := by
  have hu := orderEmbOfFin_unique h' (f := fun i => e (A.orderEmbOfFin h i))
    (fun i => Finset.mem_map_of_mem e.toEmbedding (orderEmbOfFin_mem A h i))
    (e.strictMono.comp (A.orderEmbOfFin h).strictMono)
  exact (congrFun hu i).symm

/-- Minors of a matrix reindexed along an order embedding `e : Fin m ↪o Fin n` (in rows and
columns) are minors of the original matrix with rows and columns `A.map e`, `B.map e`. -/
theorem minor_submatrix_orderEmb {m : ℕ} (e : Fin m ↪o Fin n) (X : Matrix (Fin n) (Fin n) R)
    (A B : Finset (Fin m)) :
    minor (X.submatrix e e) A B = minor X (A.map e.toEmbedding) (B.map e.toEmbedding) := by
  by_cases hc : A.card = B.card
  · have hA : (A.map e.toEmbedding).card = A.card := Finset.card_map _
    have hB : (B.map e.toEmbedding).card = A.card := by rw [Finset.card_map, hc]
    rw [minor_eq rfl hc.symm, minor_eq hA hB]
    congr 1
    ext i j
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.submatrix_apply,
      orderEmbOfFin_map e A rfl hA, orderEmbOfFin_map e B hc.symm hB]
  · rw [minor_of_card_ne hc, minor_of_card_ne (by rwa [Finset.card_map, Finset.card_map])]

/-- The case of `Fin.castSucc`: minors of the upper left `n × n` block of an
`(n + 1) × (n + 1)` matrix. -/
theorem minor_submatrix_castSucc (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (A B : Finset (Fin n)) :
    minor (X.submatrix Fin.castSucc Fin.castSucc) A B =
      minor X (A.map Fin.castSuccEmb) (B.map Fin.castSuccEmb) :=
  minor_submatrix_orderEmb Fin.castSuccOrderEmb X A B

/-! ## Ring homomorphisms and continuity -/

theorem minor_map {S : Type*} [CommRing S] (f : R →+* S) (X : Matrix (Fin n) (Fin n) R)
    (A B : Finset (Fin n)) : minor (X.map f) A B = f (minor X A B) := by
  by_cases hc : A.card = B.card
  · rw [minor_eq rfl hc.symm, minor_eq rfl hc.symm, RingHom.map_det]
    rfl
  · rw [minor_of_card_ne hc, minor_of_card_ne hc, map_zero]

theorem continuous_minor [TopologicalSpace R] [IsTopologicalRing R] (A B : Finset (Fin n)) :
    Continuous fun X : Matrix (Fin n) (Fin n) R => minor X A B := by
  by_cases hc : A.card = B.card
  · simp_rw [minor_eq rfl hc.symm]
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  · simp_rw [minor_of_card_ne hc]
    exact continuous_const

/-! ## Jacobi's complementary minor theorem, principal case -/

/-- The increasing enumeration of `S` as an equivalence onto the subtype `{i // i ∈ S}`. -/
def subtypeEquiv (S : Finset (Fin n)) : Fin S.card ≃ {i // i ∈ S} :=
  Equiv.ofBijective (fun r => ⟨S.orderEmbOfFin rfl r, orderEmbOfFin_mem _ _ _⟩)
    ⟨fun r s h => (S.orderEmbOfFin rfl).injective (congrArg Subtype.val h), fun i => by
      have hi : (i : Fin n) ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [range_orderEmbOfFin]
        exact i.2
      obtain ⟨r, hr⟩ := hi
      exact ⟨r, Subtype.ext hr⟩⟩

/-- A principal minor is the determinant of the submatrix indexed by the subtype. -/
theorem minor_eq_det_subtype (X : Matrix (Fin n) (Fin n) R) (S : Finset (Fin n)) :
    minor X S S = (X.submatrix (fun i : {i // i ∈ S} => (i : Fin n))
      (fun i : {i // i ∈ S} => (i : Fin n))).det := by
  rw [minor_eq rfl rfl, ← Matrix.det_submatrix_equiv_self (subtypeEquiv S)]
  rfl

/-- If the columns of `W` with indices in `S` are those of the identity matrix, then `det W`
is the principal minor of `W` on the complement of `S`. -/
theorem det_eq_minor_compl_of_cols_eq_one {W : Matrix (Fin n) (Fin n) R} {S : Finset (Fin n)}
    (h : ∀ i, ∀ j ∈ S, W i j = (1 : Matrix (Fin n) (Fin n) R) i j) :
    W.det = minor W Sᶜ Sᶜ := by
  let b : Fin n → Bool := fun i => decide (i ∉ S)
  have hb : W.BlockTriangular b := by
    intro i j hij
    have hj : j ∈ S := by simpa [b] using (Bool.lt_iff.mp hij).1
    have hi : i ∉ S := by simpa [b] using (Bool.lt_iff.mp hij).2
    rw [h i j hj, Matrix.one_apply_ne]
    rintro rfl
    exact hi hj
  rw [hb.det_fintype, Fintype.prod_bool]
  have hfalse : (W.toSquareBlock b false).det = 1 := by
    have : W.toSquareBlock b false = 1 := by
      ext i j
      have hj : (j : Fin n) ∈ S := by simpa [b] using j.2
      rw [Matrix.toSquareBlock_def, Matrix.of_apply, h _ _ hj]
      by_cases hij : i = j
      · subst hij
        simp
      · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne fun e => hij (Subtype.ext e)]
    rw [this, Matrix.det_one]
  rw [hfalse, mul_one, minor_eq_det_subtype]
  let e : {i // b i = true} ≃ {i // i ∈ Sᶜ} :=
    Equiv.subtypeEquivRight fun i => by simp [b]
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

/-- **Jacobi's complementary minor theorem, principal case.** If `X * Y = 1`, then
`det X · det Y_{A,A} = det X_{Aᶜ,Aᶜ}`. -/
theorem det_mul_minor_of_mul_eq_one {X Y : Matrix (Fin n) (Fin n) R} (h : X * Y = 1)
    (A : Finset (Fin n)) : X.det * minor Y A A = minor X Aᶜ Aᶜ := by
  classical
  let Z : Matrix (Fin n) (Fin n) R :=
    Matrix.of fun i j => if j ∈ A then Y i j else (1 : Matrix (Fin n) (Fin n) R) i j
  have hXZ (i j : Fin n) : (X * Z) i j = if j ∈ A then (1 : Matrix (Fin n) (Fin n) R) i j
      else X i j := by
    by_cases hj : j ∈ A
    · rw [ite_eq_left hj, ← h, Matrix.mul_apply, Matrix.mul_apply]
      simp [Z, hj]
    · rw [ite_eq_right hj, Matrix.mul_apply]
      simp [Z, hj, Matrix.one_apply]
  have hW : (X * Z).det = minor X Aᶜ Aᶜ := by
    rw [det_eq_minor_compl_of_cols_eq_one (S := A) fun i j hj => by rw [hXZ, ite_eq_left hj]]
    exact minor_congr fun i _ j hj => by
      rw [hXZ, ite_eq_right (Finset.mem_compl.mp hj)]
  have hZ : Z.det = minor Y A A := by
    rw [det_eq_minor_compl_of_cols_eq_one (S := Aᶜ) fun i j hj => by
      simp [Z, Finset.mem_compl.mp hj], compl_compl]
    exact minor_congr fun i _ j hj => by simp [Z, hj]
  rw [← hZ, ← Matrix.det_mul, hW]

/-- For an orthogonal matrix (`X * Xᵀ = 1`), a principal minor is `det X` times the
complementary principal minor. -/
theorem minor_eq_det_mul_minor_compl {X : Matrix (Fin n) (Fin n) R} (h : X * Xᵀ = 1)
    (A : Finset (Fin n)) : minor X A A = X.det * minor X Aᶜ Aᶜ := by
  have hJ := det_mul_minor_of_mul_eq_one h A
  rw [minor_transpose] at hJ
  have hdet : X.det * X.det = 1 := by
    have hd := congrArg Matrix.det h
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
  rw [← hJ, ← mul_assoc, hdet, one_mul]

end Langlands.Archimedean.MatrixMinor
