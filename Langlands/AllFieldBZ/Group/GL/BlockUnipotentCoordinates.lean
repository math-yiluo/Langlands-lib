import Langlands.AllFieldBZ.Group.GL.PadicBlocks
import Langlands.Group.GL.BlockUnipotentCoordinates

/-!
# All-field port of `Langlands.Group.GL.BlockUnipotentCoordinates`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.BlockUnipotentCoordinates` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
open scoped BigOperators
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe u

variable {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n)

variable (R : Type u) [CommRing R]

private theorem _root_.Langlands.GeneralLinear.BlockShape.index_apply (i : Fin B.length) (a : Fin (B.size i)) :
    B.index i a = B.indexEquiv ⟨i, a⟩ := rfl

private theorem _root_.Langlands.GeneralLinear.BlockShape.sigmaRadicalMatrix_blockTriangular (X : B.RadicalCoordinates R) :
    (B.sigmaRadicalMatrix R X).BlockTriangular Sigma.fst := by
  intro x y hyx
  have hxy : x ≠ y := fun h => lt_irrefl y.1 (h ▸ hyx)
  have hlt : ¬x.1 < y.1 := not_lt.mpr hyx.le
  simp only [sigmaRadicalMatrix]
  rw [ite_eq_right hxy, dite_eq_right hlt]

private theorem _root_.Langlands.GeneralLinear.BlockShape.det_sigmaRadicalMatrix (X : B.RadicalCoordinates R) :
    (B.sigmaRadicalMatrix R X).det = 1 := by
  rw [(B.sigmaRadicalMatrix_blockTriangular R X).det]
  refine Finset.prod_eq_one fun k _ => ?_
  have h1 : (B.sigmaRadicalMatrix R X).toSquareBlock Sigma.fst k = 1 := by
    ext x y
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply]
    have hxy : x.1.1 = y.1.1 := x.2.trans y.2.symm
    by_cases h : x = y
    · rw [ite_eq_left h, h]
      simp only [sigmaRadicalMatrix, ite_true]
    · have h' : x.1 ≠ y.1 := fun e => h (Subtype.ext e)
      have hlt : ¬x.1.1 < y.1.1 := by
        rw [hxy]
        exact lt_irrefl _
      rw [ite_eq_right h]
      simp only [sigmaRadicalMatrix]
      rw [ite_eq_right h', dite_eq_right hlt]
  rw [h1, Matrix.det_one]

private theorem _root_.Langlands.GeneralLinear.BlockShape.radicalMatrix_apply_indexEquiv (X : B.RadicalCoordinates R) (x y : B.Index) :
    B.radicalMatrix R X (B.indexEquiv x) (B.indexEquiv y) = B.sigmaRadicalMatrix R X x y := by
  change Matrix.reindex B.indexEquiv B.indexEquiv (B.sigmaRadicalMatrix R X)
    (B.indexEquiv x) (B.indexEquiv y) = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

private theorem _root_.Langlands.GeneralLinear.BlockShape.sum_dite_zero {ι M : Type*} [Fintype ι] [AddCommMonoid M] (p : ι → Prop)
    [DecidablePred p] (f : ∀ x, p x → M) :
    ∑ x, (if h : p x then f x h else 0) = ∑ x : {x // p x}, f x x.2 := by
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  rw [Finset.sum_eq_zero (s := Finset.univ) (fun (x : {x // ¬p x}) _ => dite_eq_right x.2), add_zero]
  exact Finset.sum_congr rfl fun x _ => dite_eq_left x.2

private theorem _root_.Langlands.GeneralLinear.BlockShape.mul_apply_index (A C : Matrix (Fin n) (Fin n) R) (x y : Fin n) :
    (A * C) x y = ∑ k : Fin B.length, ∑ c : Fin (B.size k), A x (B.index k c) * C (B.index k c) y := by
  rw [Matrix.mul_apply, ← B.indexEquiv.sum_comp, Fintype.sum_sigma]
  rfl

private theorem _root_.Langlands.GeneralLinear.BlockShape.block_product_term (u v : B.unipotentRadical R) {i j : Fin B.length}
    (hij : i < j) (a : Fin (B.size i)) (b : Fin (B.size j)) (k : Fin B.length) :
    ∑ c : Fin (B.size k),
        u.val.val (B.index i a) (B.index k c) * v.val.val (B.index k c) (B.index j b) =
      (if k = i then v.val.val (B.index i a) (B.index j b) else 0) +
        (if k = j then u.val.val (B.index i a) (B.index j b) else 0) +
        (if h : i < k ∧ k < j then
          (B.radicalCoordinates R u ⟨(i, k), h.1⟩ * B.radicalCoordinates R v ⟨(k, j), h.2⟩) a b
        else 0) := by
  have hu := (B.mem_unipotentRadical_iff R u.val).mp u.property
  have hv := (B.mem_unipotentRadical_iff R v.val).mp v.property
  have pu := (B.mem_parabolic_iff R u.val.val).mp u.val.property
  have pv := (B.mem_parabolic_iff R v.val.val).mp v.val.property
  rcases lt_trichotomy k i with hki | rfl | hik
  · rw [ite_eq_right hki.ne, ite_eq_right (hki.trans hij).ne,
      dite_eq_right fun h => (lt_asymm hki h.1).elim, add_zero, add_zero]
    exact Finset.sum_eq_zero fun c _ => by rw [pu i k a c hki, zero_mul]
  · rw [ite_eq_left rfl, ite_eq_right hij.ne, dite_eq_right fun h => (lt_irrefl _ h.1).elim, add_zero, add_zero]
    simp only [hu, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · rcases lt_trichotomy k j with hkj | rfl | hjk
    · rw [ite_eq_right hik.ne', ite_eq_right hkj.ne, dite_eq_left ⟨hik, hkj⟩, zero_add, zero_add, Matrix.mul_apply]
      rfl
    · rw [ite_eq_right hik.ne', ite_eq_left rfl, dite_eq_right fun h => (lt_irrefl _ h.2).elim, zero_add, add_zero]
      simp only [hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · rw [ite_eq_right hik.ne', ite_eq_right hjk.ne', dite_eq_right fun h => (lt_asymm hjk h.2).elim,
        add_zero, add_zero]
      exact Finset.sum_eq_zero fun c _ => by rw [pv k j c b hjk, mul_zero]

private theorem _root_.Langlands.GeneralLinear.BlockShape.leviEmbedding_mul_apply (m : B.Levi R) (A : Matrix (Fin n) (Fin n) R)
    (i : Fin B.length) (a : Fin (B.size i)) (y : Fin n) :
    ((B.leviEmbedding R m : Matrix (Fin n) (Fin n) R) * A) (B.index i a) y =
      ∑ c : Fin (B.size i), (m i).val a c * A (B.index i c) y := by
  rw [B.mul_apply_index R, Fintype.sum_eq_single i]
  · exact Finset.sum_congr rfl fun c _ => by rw [B.leviEmbedding_apply_same R m i a c]
  · intro k hk
    exact Finset.sum_eq_zero fun c _ => by
      rw [B.leviEmbedding_apply_ne R m a c (Ne.symm hk), zero_mul]

private theorem _root_.Langlands.GeneralLinear.BlockShape.mul_leviEmbedding_apply (m : B.Levi R) (A : Matrix (Fin n) (Fin n) R)
    (x : Fin n) (j : Fin B.length) (b : Fin (B.size j)) :
    (A * (B.leviEmbedding R m : Matrix (Fin n) (Fin n) R)) x (B.index j b) =
      ∑ d : Fin (B.size j), A x (B.index j d) * (m j).val d b := by
  rw [B.mul_apply_index R, Fintype.sum_eq_single j]
  · exact Finset.sum_congr rfl fun d _ => by rw [B.leviEmbedding_apply_same R m j d b]
  · intro k hk
    exact Finset.sum_eq_zero fun d _ => by
      rw [B.leviEmbedding_apply_ne R m d b hk, mul_zero]

section Topology
variable [TopologicalSpace R]

variable [IsTopologicalRing R]

omit [IsTopologicalRing R] in
private theorem _root_.Langlands.GeneralLinear.BlockShape.continuous_sigmaRadicalMatrix :
    Continuous (fun X : B.RadicalCoordinates R => B.sigmaRadicalMatrix R X) := by
  apply continuous_matrix
  intro x y
  by_cases hxy : x = y
  · simp only [sigmaRadicalMatrix, ite_eq_left hxy]
    exact continuous_const
  · by_cases hlt : x.1 < y.1
    · simp only [sigmaRadicalMatrix, ite_eq_right hxy, dite_eq_left hlt]
      exact (continuous_apply _).matrix_elem _ _
    · simp only [sigmaRadicalMatrix, ite_eq_right hxy, dite_eq_right hlt]
      exact continuous_const

end Topology
end BlockShape
end Langlands.AllFieldBZ.GeneralLinear
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe u

variable {F : LocalFieldPackage.{u}} {n : ℕ}

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
