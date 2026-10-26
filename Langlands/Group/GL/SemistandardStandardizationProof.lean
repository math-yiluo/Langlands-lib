import Langlands.Group.GL.SemistandardStandardizationStatement

/-! Determinant-matching proof of semistandard block standardization. -/

noncomputable section

open scoped BigOperators

namespace Langlands

open GeneralLinear Exponents

universe uR uF

namespace GeneralLinear.BlockShape

variable {n : ℕ} {R : Type uR} [Field R]

/-- A nonzero determinant supplies one nonzero entry in each row and column. -/
theorem exists_permutation_nonzero_entries (g : GeneralLinear n R) :
    ∃ s : Equiv.Perm (Fin n), ∀ k, g (s k) k ≠ 0 := by
  classical
  have h := Matrix.GeneralLinearGroup.det_ne_zero g
  rw [Matrix.det_apply'] at h
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨s, fun k => ?_⟩
  exact Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hs).2 k (Finset.mem_univ k)

/-- An invertible matrix with zero off-block entries lies in the embedded Levi. -/
theorem exists_levi_of_offBlock_zero (B : BlockShape n) (g : GeneralLinear n R)
    (h : ∀ (i j : Fin B.length) (r : Fin (B.size i)) (s : Fin (B.size j)),
      i ≠ j → g (B.index i r) (B.index j s) = 0) :
    ∃ m : B.Levi R, g = B.leviEmbedding R m := by
  have hp : g ∈ B.parabolic R := (B.mem_parabolic_iff R g).mpr
    (fun i j r s hji => h i j r s (ne_of_gt hji))
  refine ⟨B.leviProjection R ⟨g, hp⟩, ?_⟩
  apply Units.ext
  ext x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  change g (B.index i r) (B.index j s) =
    B.leviEmbedding R _ (B.index i r) (B.index j s)
  by_cases hij : i = j
  · subst j
    rw [B.leviEmbedding_apply_same, B.leviProjection_apply]
  · rw [h i j r s hij, B.leviEmbedding_apply_ne R _ r s hij]

end GeneralLinear.BlockShape

namespace Exponents.ConjugateBlockPair

variable {n : ℕ} {R : Type uR} [Field R] [CharZero R]

/-- Two nonzero entries in one row of a semistandard conjugator belong to
one original block. This version directly gives the needed vanishing. -/
theorem offBlock_zero_of_semistandard (P : ConjugateBlockPair n R)
    (h : P.splitComponent ≤
      (standard (R := R) (BlockShape.singletons n)).splitComponent)
    (k : Fin n) (i j : Fin P.shape.length)
    (r : Fin (P.shape.size i)) (s : Fin (P.shape.size j))
    (hpivot : P.conjugator k (P.shape.index i r) ≠ 0) (hij : i ≠ j) :
    P.conjugator k (P.shape.index j s) = 0 := by
  classical
  let a : Fin P.shape.length → Rˣ :=
    fun l => if l = i then Units.mk0 2 (by norm_num) else 1
  obtain ⟨b, hb⟩ := h (show P.scalarMap a ∈ P.splitComponent from ⟨a, rfl⟩)
  change Fin n → Rˣ at b
  have hm : (BlockShape.singletons n).blockScalar R b * P.conjugator =
      P.conjugator * P.shape.blockScalar R a := by
    change (standard (R := R) (BlockShape.singletons n)).scalarMap b = P.scalarMap a at hb
    rw [standard_scalarMap] at hb
    change (BlockShape.singletons n).blockScalar R b =
      P.conjugator * P.shape.blockScalar R a * P.conjugator⁻¹ at hb
    rw [hb, mul_assoc, inv_mul_cancel, mul_one]
  have he : ∀ (l : Fin P.shape.length) (v : Fin (P.shape.size l)),
      (b k : R) * P.conjugator k (P.shape.index l v) =
        P.conjugator k (P.shape.index l v) * (a l : R) := by
    intro l v
    have hv := congrArg (fun g : GeneralLinear n R => g k (P.shape.index l v)) hm
    change (((BlockShape.singletons n).blockScalar R b).val * P.conjugator.val)
      k (P.shape.index l v) =
      (P.conjugator.val * (P.shape.blockScalar R a).val) k (P.shape.index l v) at hv
    rw [show ((BlockShape.singletons n).blockScalar R b).val =
      Matrix.diagonal (fun x => (b x : R)) from
        BlockShape.leviEmbedding_singletonLevi_val R b,
      P.shape.coe_blockScalar, Matrix.diagonal_mul, Matrix.mul_diagonal] at hv
    simpa only [show P.shape.indexEquiv.symm (P.shape.index l v) = ⟨l, v⟩ from
      P.shape.indexEquiv.symm_apply_apply ⟨l, v⟩] using hv
  have hbval : (b k : R) = 2 := by
    have hi := he i r
    simp only [a, ite_eq_left rfl, Units.val_mk0] at hi
    exact (mul_right_cancel₀ hpivot) (hi.trans (mul_comm _ _))
  have hj := he j s
  simp only [a, ite_eq_right hij.symm, Units.val_one, mul_one, hbval] at hj
  linear_combination hj

/-- Over characteristic-zero fields, a semistandard conjugator becomes an
actual element of the original ordered Levi after a permutation of its rows. -/
theorem exists_permutation_standardizer (P : ConjugateBlockPair n R)
    (h : P.splitComponent ≤
      (standard (R := R) (BlockShape.singletons n)).splitComponent) :
    ∃ (w : Equiv.Perm (Fin n)) (m : P.shape.Levi R),
      GeneralLinear.permutation n R w * P.conjugator = P.shape.leviEmbedding R m := by
  obtain ⟨s, hs⟩ := BlockShape.exists_permutation_nonzero_entries P.conjugator
  refine ⟨s⁻¹, ?_⟩
  apply P.shape.exists_levi_of_offBlock_zero
  intro i j r t hij
  rw [GeneralLinear.permutation_mul_entry, inv_inv]
  exact P.offBlock_zero_of_semistandard h _ i j r t (hs _) hij

end Exponents.ConjugateBlockPair

/-- Exact p-adic specialization, preserving the arbitrary field universe. -/
theorem glSemistandardStandardization : GLSemistandardStandardizationStatement.{uF} := by
  intro p _ F n P h
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact P.exists_permutation_standardizer h

end Langlands
