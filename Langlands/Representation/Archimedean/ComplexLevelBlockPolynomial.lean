import Langlands.Representation.Archimedean.ComplexLevelSpan
import Langlands.Representation.Archimedean.ComplexBlockPolynomial

/-!
# Level products are polynomial along the root subgroup of their GL_2 block

Let `i < r` with `r = i + 1`, and consider the root elements `1 + z E_{r,i}`. Left
multiplication by them changes the rows `m, …, n-1` of a matrix only through a unipotent
matrix when `m ≠ r` (`tailRows_rootMatrix_mul`), so every level factor with `m ≠ r` is invariant.
At the level `r` every determinant factor is affine in `z` (`levelDet_rootMatrix_mul_affine`).
Hence a level product whose Gram exponent at level `r` vanishes and which has `h_r < p`
holomorphic and `b_r < q` antiholomorphic determinant factors there is block-polynomial of
bidegree `< (p, q)` (`isBlockPoly_levelProduct`), and so is every element of the level span.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean.LevelFunctions

open Langlands.Archimedean.ComplexDuality Langlands.GeneralLinear
open Langlands.Archimedean.BlockPolynomial

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- Rows `m, …` of `b y` only see rows `m, …` of `y` when `b` has no entries from rows `≥ m` to
columns `< m`. -/
theorem tailRows_mul_of_zero (m : ℕ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : ∀ a k : Fin n, m ≤ (a : ℕ) → ¬ m ≤ (k : ℕ) → b a k = 0) (y : Matrix (Fin n) (Fin n) ℂ) :
    tailRows m (b * y) =
      b.submatrix (Subtype.val : Tail n m → Fin n) Subtype.val * tailRows m y := by
  ext a j
  simp only [tailRows, Matrix.of_apply, Matrix.mul_apply, Matrix.submatrix_apply]
  have hz : ∑ k : {k : Fin n // ¬ m ≤ (k : ℕ)}, b a (k : Fin n) * y (k : Fin n) j = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hb a k a.2 k.2, zero_mul]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k : Fin n => m ≤ (k : ℕ)), hz, add_zero]

variable {i r : Fin n}

theorem rootMatrix_zero_of_ne (hr : (r : ℕ) = (i : ℕ) + 1) (m : ℕ) (hm : m ≠ (r : ℕ)) (z : ℂ) :
    ∀ a k : Fin n, m ≤ (a : ℕ) → ¬ m ≤ (k : ℕ) → rootMatrix i r z a k = 0 := by
  intro a k ha hk
  have hak : a ≠ k := fun h => hk (h ▸ ha)
  simp only [rootMatrix, Matrix.add_apply, Matrix.one_apply_ne hak, Matrix.single_apply,
    zero_add]
  rw [ite_eq_right_iff]
  rintro ⟨rfl, rfl⟩
  omega

theorem det_rootMatrix_submatrix (hr : (r : ℕ) = (i : ℕ) + 1) (m : ℕ) (z : ℂ) :
    ((rootMatrix i r z).submatrix (Subtype.val : Tail n m → Fin n) Subtype.val).det = 1 := by
  have hir : i ≠ r := fun h => by rw [h] at hr; omega
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp only [Matrix.submatrix_apply, rootMatrix, Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.single_apply]
    rw [ite_eq_right_iff.2, add_zero]
    rintro ⟨h1, h2⟩
    exact absurd (h2.trans h1.symm) hir
  · intro a k hak
    have hak2 : a < k := hak
    have hak' : (a : Fin n) ≠ k := fun h => (ne_of_lt hak2) (Subtype.ext h)
    simp only [Matrix.submatrix_apply, rootMatrix, Matrix.add_apply, Matrix.one_apply_ne hak',
      Matrix.single_apply, zero_add]
    rw [ite_eq_right_iff]
    rintro ⟨h1, h2⟩
    have h3 : ((a : Fin n) : ℕ) < ((k : Fin n) : ℕ) := hak2
    rw [← h1, ← h2] at h3
    omega

theorem levelDet_rootMatrix_mul (hr : (r : ℕ) = (i : ℕ) + 1) (m : ℕ) (hm : m ≠ (r : ℕ))
    (z : ℂ) (A : Matrix (Fin n) (Tail n m) ℂ) (y : Matrix (Fin n) (Fin n) ℂ) :
    levelDet m A (rootMatrix i r z * y) = levelDet m A y := by
  rw [levelDet, tailRows_mul_of_zero m (rootMatrix_zero_of_ne hr m hm z), Matrix.mul_assoc,
    Matrix.det_mul, det_rootMatrix_submatrix hr, one_mul, levelDet]

theorem gramMinor_rootMatrix_mul (hr : (r : ℕ) = (i : ℕ) + 1) (m : ℕ) (hm : m ≠ (r : ℕ)) (z : ℂ)
    (y : Matrix (Fin n) (Fin n) ℂ) : gramMinor m (rootMatrix i r z * y) = gramMinor m y := by
  set U := (rootMatrix i r z).submatrix (Subtype.val : Tail n m → Fin n) Subtype.val
  have hT : tailRows m (rootMatrix i r z * y) = U * tailRows m y :=
    tailRows_mul_of_zero m (rootMatrix_zero_of_ne hr m hm z) y
  have hU : U.det = 1 := det_rootMatrix_submatrix hr m z
  have : tailGram m (rootMatrix i r z * y) = tailGram m y := by
    rw [tailGram, hT, Matrix.conjTranspose_mul, show U * tailRows m y *
        ((tailRows m y)ᴴ * Uᴴ) = U * (tailRows m y * (tailRows m y)ᴴ) * Uᴴ by
        simp only [Matrix.mul_assoc],
      Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hU, star_one, one_mul, mul_one,
      tailGram]
  rw [gramMinor, this, gramMinor]

/-- At the level `r = i + 1` every determinant factor is affine in `z`. -/
theorem levelDet_rootMatrix_mul_affine (A : Matrix (Fin n) (Tail n r) ℂ) (y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ c₀ c₁ : ℂ, ∀ z, levelDet r A (rootMatrix i r z * y) = c₀ + c₁ * z := by
  set j₀ : Tail n r := ⟨r, le_rfl⟩
  set T := tailRows (r : ℕ) y * A
  let W : Matrix (Tail n r) (Fin n) ℂ := Matrix.of fun a k => if a = j₀ then y i k else 0
  have hrow : ∀ z, tailRows (r : ℕ) (rootMatrix i r z * y) = tailRows (r : ℕ) y + z • W := by
    intro z
    ext a k
    simp only [tailRows, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, W,
      rootMatrix, Matrix.add_mul, Matrix.one_mul]
    by_cases ha : a = j₀
    · subst ha
      rw [Matrix.single_mul_apply_same]
      simp
    · have hne : (a : Fin n) ≠ r := fun h => ha (Subtype.ext h)
      rw [Matrix.single_mul_apply_of_ne (h := hne)]
      simp [ha]
  refine ⟨T.det, (T.updateRow j₀ ((W * A) j₀)).det, fun z => ?_⟩
  have hTz : (tailRows (r : ℕ) y + z • W) * A = T.updateRow j₀ (T j₀ + z • (W * A) j₀) := by
    ext a k
    by_cases ha : a = j₀
    · subst ha
      rw [Matrix.updateRow_self, Matrix.add_mul, Matrix.smul_mul]
      rfl
    · rw [Matrix.updateRow_ne ha, Matrix.add_mul, Matrix.smul_mul, Matrix.add_apply,
        Matrix.smul_apply]
      have hW : (W * A) a k = 0 := by
        simp [W, Matrix.mul_apply, ha]
      rw [hW, smul_zero, add_zero]
  rw [levelDet, hrow, hTz, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.updateRow_eq_self]
  ring

theorem prod_affine_mem {κ : Type*} (s : Finset κ) (c₀ c₁ : κ → ℂ) :
    (fun z => ∏ j ∈ s, (c₀ j + c₁ j * z)) ∈ bidegLT (s.card + 1) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const_mem_bidegLT 1
  | insert j s hj ih =>
    have := affine_mul_mem ih (c₀ j) (c₁ j)
    rw [Finset.card_insert_of_notMem hj]
    convert this using 1
    funext z
    rw [Finset.prod_insert hj]

theorem prod_conj_affine_mul_mem {κ : Type*} (s : Finset κ) (c₀ c₁ : κ → ℂ) {p q : ℕ}
    {f : ℂ → ℂ} (hf : f ∈ bidegLT p q) :
    (fun z => (∏ j ∈ s, conj (c₀ j + c₁ j * z)) * f z) ∈ bidegLT p (q + s.card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | insert j s hj ih =>
    have := conj_affine_mul_mem ih (c₀ j) (c₁ j)
    rw [Finset.card_insert_of_notMem hj, ← add_assoc]
    convert this using 1
    funext z
    rw [Finset.prod_insert hj, mul_assoc]

variable (h b : ℕ → ℕ) (dτ : ℕ → ℂ)

/-- **Level products are block-polynomial** when the level `r = i + 1` has no Gram factor, fewer
than `p` holomorphic and fewer than `q` antiholomorphic determinant factors. -/
theorem isBlockPoly_levelProduct (hr : (r : ℕ) = (i : ℕ) + 1) (hir : i ≠ r) {p q : ℕ}
    (hgram : dτ r - ((h r + b r : ℕ) : ℂ) / 2 = 0) (hp : h r < p) (hq : b r < q)
    (A : LevelMatrices n h b) : IsBlockPoly hir p q (levelProduct h b dτ A) := by
  classical
  intro g
  set y := (g : Matrix (Fin n) (Fin n) ℂ)
  have hfac : ∀ m : Fin n, m ≠ r → ∀ z,
      gramPart h b dτ m (rootMatrix i r z * y) * detPart h b m (A m) (rootMatrix i r z * y) =
        gramPart h b dτ m y * detPart h b m (A m) y := by
    intro m hm z
    have hm' : (m : ℕ) ≠ (r : ℕ) := fun h' => hm (Fin.ext h')
    unfold gramPart detPart
    rw [gramMinor_rootMatrix_mul hr _ hm']
    simp only [levelDet_rootMatrix_mul hr _ hm']
  have hA := fun j => levelDet_rootMatrix_mul_affine (i := i) ((A r).1 j) y
  have hB := fun j => levelDet_rootMatrix_mul_affine (i := i) ((A r).2 j) y
  choose a₀ a₁ ha using hA
  choose b₀ b₁ hb using hB
  set C := ∏ m ∈ Finset.univ.erase r, gramPart h b dτ m y * detPart h b m (A m) y
  have heq : (fun z => levelProduct h b dτ A (rootUnit hir z * g)) = fun z =>
      C * ((∏ j : Fin (b r), conj (b₀ j + b₁ j * z)) * ∏ j : Fin (h r), (a₀ j + a₁ j * z)) := by
    funext z
    simp only [levelProduct, levelProductExt, Units.val_mul, rootUnit_val]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
    rw [Finset.prod_congr rfl fun m hm => hfac m (Finset.ne_of_mem_erase hm) z]
    have hg : gramPart h b dτ r (rootMatrix i r z * y) = 1 := by
      unfold gramPart; rw [hgram, Complex.cpow_zero]
    have hd : detPart h b r (A r) (rootMatrix i r z * y) =
        (∏ j : Fin (h r), (a₀ j + a₁ j * z)) * ∏ j : Fin (b r), conj (b₀ j + b₁ j * z) := by
      unfold detPart
      simp only [ha, hb]
    rw [hg, hd]
    ring
  rw [heq]
  refine Submodule.smul_mem _ C ?_
  have h1 := prod_conj_affine_mul_mem Finset.univ b₀ b₁ (prod_affine_mem Finset.univ a₀ a₁)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  exact bidegLT_mono (by omega) (by omega) h1

theorem isBlockPoly_of_mem_levelSpan (hr : (r : ℕ) = (i : ℕ) + 1) (hir : i ≠ r) {p q : ℕ}
    (hgram : dτ r - ((h r + b r : ℕ) : ℂ) / 2 = 0) (hp : h r < p) (hq : b r < q)
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ levelSpan (n := n) h b dτ) :
    IsBlockPoly hir p q f := by
  have : levelSpan (n := n) h b dτ ≤ blockPolySubmodule hir p q := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨A, rfl⟩
    exact isBlockPoly_levelProduct h b dτ hr hir hgram hp hq A
  exact this hf

end Langlands.Archimedean.LevelFunctions
