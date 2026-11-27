import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisInduction
import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisCongruence
import Langlands.GroupScheme.Quaternionic.SkewHermitianOrthogonalBasis
import Langlands.GroupScheme.Quaternionic.HyperbolicBasis
import Langlands.GroupScheme.Quaternionic.KneserThreeQuaternion

/-! # Assembly of the special unitary Hasse principle

An invertible antihermitian Gram matrix over a division algebra with nontrivial involution is
congruent to a diagonal matrix with nonzero alternating entries, hence to a matrix obtained by
adjoining a skew line. Together with transport along congruences, this turns the inductive
step for adjoined lines into the inductive step for all Gram matrices; the induction starts in
rank one.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

section Diagonal

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] (τ : FirstKindInvolution F D)

/-- A diagonal matrix with alternating entries is antihermitian. -/
theorem isAntihermitian_diagonal {n : ℕ} (d : Fin n → D)
    (hd : ∀ i, d i ∈ τ.alternatingSubspace) : τ.IsAntihermitian (Matrix.diagonal d) := by
  refine ⟨?_, fun i => by rw [Matrix.diagonal_apply_eq]; exact hd i⟩
  ext i j
  rw [FirstKindInvolution.matrix_apply, Matrix.neg_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    obtain ⟨a, ha⟩ := τ.mem_alternatingSubspace.mp (hd i)
    rw [← ha, τ.map_sub, τ.apply_apply, neg_sub]
  · rw [Matrix.diagonal_apply_ne _ (Ne.symm hij), Matrix.diagonal_apply_ne _ hij, τ.map_zero,
      neg_zero]

/-- A diagonal matrix is obtained from its upper left block by adjoining its last entry. -/
theorem diagonal_eq_adjoinSkewLine {A : Type*} [Ring A] {m : ℕ} (d : Fin (m + 1) → A) :
    Matrix.diagonal d =
      adjoinSkewLine (Matrix.diagonal (fun i => d i.castSucc)) (d (Fin.last m)) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [adjoinSkewLine_last, Matrix.diagonal_apply_eq]
    · rw [adjoinSkewLine_last_castSucc, Matrix.diagonal_apply_ne _ (Fin.castSucc_lt_last j).ne']
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [adjoinSkewLine_castSucc_last, Matrix.diagonal_apply_ne _ (Fin.castSucc_lt_last i).ne]
    · rw [adjoinSkewLine_castSucc]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ hij,
          Matrix.diagonal_apply_ne _ (fun h => hij (Fin.castSucc_injective _ h))]

/-- An invertible antihermitian Gram matrix for a nontrivial involution is congruent to a
diagonal matrix with nonzero alternating entries. -/
theorem exists_diagonal_congr (hτ : ∃ a, τ a ≠ a) {n : ℕ} (H : Matrix (Fin n) (Fin n) D)
    (hH : τ.IsAntihermitian H) (hu : IsUnit H) :
    ∃ (P : (Matrix (Fin n) (Fin n) D)ˣ) (d : Fin n → D),
      (∀ i, d i ∈ τ.alternatingSubspace) ∧ (∀ i, d i ≠ 0) ∧
        (P : Matrix (Fin n) (Fin n) D) * H * τ.matrix (Fin n) P = Matrix.diagonal d := by
  let B := AntihermitianForm.ofMatrix hH
  have hB := AntihermitianForm.ofMatrix_separatingLeft hH hu
  obtain ⟨b, hb, hd⟩ := AntihermitianForm.orthogonalBasis F D τ (Fin n → D) B hτ hB
  let e := finCongr (Module.finrank_fin_fun D (n := n))
  let c := b.reindex e
  have hc (i : Fin n) : c i = b (e.symm i) := Module.Basis.reindex_apply b e i
  let P : Matrix (Fin n) (Fin n) D := Matrix.of fun i => c i
  let d : Fin n → D := fun i => τ.sesqForm H (c i) (c i)
  have hd0 (i : Fin n) : d i ≠ 0 := by
    change B (c i) (c i) ≠ 0
    rw [hc]
    exact hd _
  have hP : P * H * τ.matrix (Fin n) P = Matrix.diagonal d := by
    ext i j
    rw [τ.mul_mul_matrix_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hij]
      change B (c i) (c j) = 0
      rw [hc, hc]
      exact hb _ _ (fun h => hij (e.symm.injective h))
  have hdu : IsUnit (Matrix.diagonal d) :=
    (Pi.isUnit_iff.mpr fun i => isUnit_iff_ne_zero.mpr (hd0 i)).map
      (Matrix.diagonalRingHom (Fin n) D)
  have hPu : IsUnit P := τ.isUnit_of_mul_mul_matrix_eq hdu hP
  refine ⟨hPu.unit, d, fun i => τ.sesqForm_self_mem_alternatingSubspace hH (c i), hd0, ?_⟩
  rw [IsUnit.unit_spec]
  exact hP

end Diagonal

section Assembly

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D]
  [FiniteDimensional F D] [NumberField F]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

omit [NumberField F] [Algebra.IsCentral F D] in
/-- The canonical conjugation of a quaternion algebra in characteristic zero is nontrivial. -/
theorem quaternionConjugation_ne_id [CharZero F] :
    ∃ a : D, σ.quaternionConjugation hdim hsym a ≠ a := by
  let l := σ.quaternionAlternatingUnit hdim hsym
  refine ⟨(l : D), ?_⟩
  rw [KneserThree.Quaternion.conj_ell]
  intro hh
  have h := congrArg (fun z : D => z + l) hh
  rw [neg_add_cancel, ← two_smul F] at h
  exact (smul_ne_zero (two_ne_zero : (2 : F) ≠ 0) l.ne_zero) h.symm

/-- The inductive step for all Gram matrices of size `m + 1`. -/
theorem suHasse_succ {m : ℕ} [NeZero m]
    (hW : ∀ (K : Type u) [Field K] [Algebra F K] [CharZero K],
      ProperWittAt (σ.quaternionConjugation hdim hsym) K (m + 1))
    (IH : SUHasse σ hdim hsym m) : SUHasse σ hdim hsym (m + 1) := by
  set τ := σ.quaternionConjugation hdim hsym
  intro H hH hu
  obtain ⟨P, d, hdalt, hd0, hP⟩ :=
    exists_diagonal_congr τ (quaternionConjugation_ne_id σ hdim hsym) H hH hu
  rw [diagonal_eq_adjoinSkewLine] at hP
  set H₁ : Matrix (Fin m) (Fin m) D := Matrix.diagonal (fun i => d i.castSucc)
  have hH₁ : τ.IsAntihermitian H₁ := isAntihermitian_diagonal τ _ (fun i => hdalt _)
  have hu₁ : IsUnit H₁ := by
    have hv : IsUnit (fun i : Fin m => d i.castSucc) :=
      Pi.isUnit_iff.mpr fun i => isUnit_iff_ne_zero.mpr (hd0 i.castSucc)
    exact hv.map (Matrix.diagonalRingHom (Fin m) D)
  have hA : HasseFor τ (adjoinSkewLine H₁ (d (Fin.last m))) :=
    fun L _ _ _ _ c hc hsu hloc => suHasse_adjoin σ hdim hsym hW IH H₁ (d (Fin.last m)) hH₁ hu₁
      (hdalt _) (hd0 _) L c hc hsu hloc
  have h := hA.congr τ P⁻¹
  rw [← hP, inv_congr_gram] at h
  exact h

/-- The special unitary Hasse principle in every rank, from rank one and proper Witt
transitivity in every rank at least two. -/
theorem suHasse_of_rankOne
    (hW : ∀ (N : ℕ) [NeZero N], 2 ≤ N → ∀ (K : Type u) [Field K] [Algebra F K] [CharZero K],
      ProperWittAt (σ.quaternionConjugation hdim hsym) K N)
    (h1 : SUHasse σ hdim hsym 1) (m : ℕ) : SUHasse σ hdim hsym (m + 1) := by
  induction m with
  | zero => exact h1
  | succ m ih => exact suHasse_succ σ hdim hsym (hW (m + 1 + 1) (by omega)) ih

end Assembly

end Langlands.GroupScheme.Quaternionic.SkewUnitary
