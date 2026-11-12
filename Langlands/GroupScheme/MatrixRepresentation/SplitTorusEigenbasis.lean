import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # A universal split-torus eigenbasis containing a prescribed eigenvector -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.GeneralLinear.CocharacterDiagonal

variable {k : Type u} [Field k]
  {n : Type} [Fintype n] [DecidableEq n]
  (I : Type u) [Fintype I] [DecidableEq I]
  (ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of k)) I) n)

/-- The given vector is a weight vector for the exponent on every coefficient algebra. -/
def IsExponentVector (m : I → ℤ) (v : n → k) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ),
    (matrixAt I ρ t : Matrix n n A) *ᵥ (fun a => algebraMap k A (v a)) =
      (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : A) •
        (fun a => algebraMap k A (v a))

/-- Any nonzero universal weight vector can be retained in a universal weight basis. -/
theorem exists_exponentBasis_containing
    (m : I → ℤ) (v : n → k) (hv : v ≠ 0) (hweight : IsExponentVector I ρ m v) :
    ∃ (b : Module.Basis n k (n → k)) (w : n → (I → ℤ)) (j : n),
      b j = v ∧ w j = m ∧ ∀ a, IsExponentVector I ρ (w a) (b a) := by
  classical
  let S : Set (n → k) :=
    insert v (Set.range (fun q : (I → ℤ) × n => coefficientColumn I ρ q.1 q.2))
  have hs : LinearIndepOn k id {v} := (linearIndepOn_singleton_iff k).mpr hv
  have hsub : ({v} : Set (n → k)) ⊆ S := Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
  have hspan : ⊤ ≤ Submodule.span k S := by
    rw [← span_coefficientColumn I ρ]
    exact Submodule.span_mono (Set.subset_insert _ _)
  let b₀ := Module.Basis.extendLe hs hsub hspan
  let f := b₀.indexEquiv (Pi.basisFun k n)
  let b := b₀.reindex f
  have hbS (a : n) : b a ∈ S := by
    apply Module.Basis.extendLe_subset hs hsub hspan
    exact ⟨f.symm a, (b₀.reindex_apply f a).symm⟩
  have hvb : v ∈ Set.range b₀ := Module.Basis.subset_extendLe hs hsub hspan (by simp)
  obtain ⟨j₀, hj₀⟩ := hvb
  let j := f j₀
  have hj : b j = v := by
    simpa only [b, j, Module.Basis.reindex_apply, Equiv.symm_apply_apply] using hj₀
  have hweights (a : n) : ∃ r : I → ℤ, IsExponentVector I ρ r (b a) := by
    rcases hbS a with h | h
    · rw [h]
      exact ⟨m, hweight⟩
    · obtain ⟨q, hq⟩ := h
      rw [← hq]
      exact ⟨q.1, fun A _ _ t => coefficientColumn_weight I ρ t q.1 q.2⟩
  choose w hw using hweights
  refine ⟨b, Function.update w j m, j, hj, by simp, ?_⟩
  intro a
  by_cases ha : a = j
  · subst a
    simpa only [Function.update_self, hj] using hweight
  · simpa only [Function.update_of_ne ha] using hw a

/-- Diagonalization can retain a chosen eigenvector as a specified matrix column,
with its original exponent. -/
theorem exists_diagonalizingMatrix_containing
    (m : I → ℤ) (v : n → k) (hv : v ≠ 0) (hweight : IsExponentVector I ρ m v) :
    ∃ (B : GL n k) (w : n → (I → ℤ)) (j : n),
      (B : Matrix n n k).col j = v ∧ w j = m ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ),
        (Matrix.GeneralLinearGroup.map (algebraMap k A) B)⁻¹ *
            matrixAt I ρ t * Matrix.GeneralLinearGroup.map (algebraMap k A) B =
          diagonalMatrix
            (fun a => splitTorus.exponentValue I t (Multiplicative.ofAdd (w a))) := by
  classical
  obtain ⟨b, w, j, hj, hwj, hw⟩ := exists_exponentBasis_containing I ρ m v hv hweight
  let std := Pi.basisFun k n
  let B : GL n k :=
    ⟨std.toMatrix b, b.toMatrix std,
      std.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip std⟩
  have hB (a s : n) : (B : Matrix n n k) a s = b s a := by
    simp [B, Module.Basis.toMatrix_apply, std]
  refine ⟨B, w, j, ?_, hwj, ?_⟩
  · ext a
    simpa only [Matrix.col_apply, hB] using congrFun hj a
  · intro A _ _ t
    let C := Matrix.GeneralLinearGroup.map (algebraMap k A) B
    let D := diagonalMatrix
      (fun a => splitTorus.exponentValue I t (Multiplicative.ofAdd (w a)))
    have hc : matrixAt I ρ t * C = C * D := by
      apply Units.ext
      ext a s
      have hs := congrFun (hw s A t) a
      change ((matrixAt I ρ t : Matrix n n A) * (C : Matrix n n A)) a s =
        ((C : Matrix n n A) * Matrix.diagonal
          (fun r => (splitTorus.exponentValue I t (Multiplicative.ofAdd (w r)) : A))) a s
      rw [Matrix.mul_diagonal]
      simp only [Matrix.mul_apply, C, Matrix.GeneralLinearGroup.map_apply, hB]
      change (∑ r, (matrixAt I ρ t : Matrix n n A) a r *
          algebraMap k A (b s r)) =
        algebraMap k A (b s a) *
          (splitTorus.exponentValue I t (Multiplicative.ofAdd (w s)) : A)
      simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_comm] using hs
    change C⁻¹ * matrixAt I ρ t * C = D
    rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]

end Langlands.GroupScheme.GeneralLinear.CocharacterDiagonal
