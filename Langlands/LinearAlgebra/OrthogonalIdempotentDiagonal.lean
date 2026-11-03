import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Simultaneous diagonalization of a complete family of orthogonal idempotent matrices -/

noncomputable section

open Module

namespace Langlands.LinearAlgebra

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*}
  [DecidableEq ι]

/-- A family of matrices `E a` with `E a * E b = if a = b then E a else 0` whose finite sum
over `s` is `1` is simultaneously conjugate to the diagonal coordinate projectors: there are an
invertible matrix `P` and a labelling `e : n → ι` with `P⁻¹ * E a * P` the diagonal matrix with
entry `1` at the coordinates labelled `a` and `0` elsewhere. -/
theorem exists_conj_eq_diagonal_of_orthogonal (E : ι → Matrix n n K)
    (hE : ∀ a b, E a * E b = if a = b then E a else 0) (s : Finset ι)
    (hs : ∑ a ∈ s, E a = 1) :
    ∃ (P : Matrix.GeneralLinearGroup n K) (e : n → ι), ∀ a,
      ((P⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) * E a * (P : Matrix n n K) =
        Matrix.diagonal fun i => if e i = a then 1 else 0 := by
  classical
  -- The weight subspaces.
  let W : ι → Submodule K (n → K) := fun a => LinearMap.range (Matrix.toLin' (E a))
  have hEW : ∀ a b (x : n → K), x ∈ W b → (E a).mulVec x = if a = b then x else 0 := by
    rintro a b x ⟨y, rfl⟩
    change (E a).mulVec ((E b).mulVec y) = if a = b then (E b).mulVec y else 0
    rw [Matrix.mulVec_mulVec, hE]
    split_ifs with h
    · rw [h]
    · exact Matrix.zero_mulVec y
  have hind : iSupIndep W := by
    rw [iSupIndep_def]
    intro a
    rw [Submodule.disjoint_def]
    intro x hxa hxo
    have hker : (⨆ (b) (_ : b ≠ a), W b) ≤ LinearMap.ker (Matrix.toLin' (E a)) := by
      refine iSup₂_le fun b hb => ?_
      intro y hy
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, hEW a b y hy]
      simp [Ne.symm hb]
    have h1 : (E a).mulVec x = x := by simp [hEW a a x hxa]
    have h2 : (E a).mulVec x = 0 := by
      have := hker hxo
      rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
    rw [← h1, h2]
  have htop : iSup W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ a ∈ s, (E a).mulVec x := by
      rw [← Matrix.sum_mulVec, hs, Matrix.one_mulVec]
    rw [hx]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.mem_iSup_of_mem a ⟨x, rfl⟩
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let B := hint.collectedBasis fun a => Basis.ofVectorSpace K (W a)
  let σ : n ≃ _ := (Pi.basisFun K n).indexEquiv B
  let B' : Basis n K (n → K) := B.reindex σ.symm
  let e : n → ι := fun i => (σ i).1
  have hB' : ∀ i, B' i ∈ W (e i) := by
    intro i
    have : B' i = B (σ i) := by
      simp only [B', Basis.reindex_apply, Equiv.symm_symm]
    rw [this]
    exact hint.collectedBasis_mem _ (σ i)
  let P0 : Matrix n n K := (Pi.basisFun K n).toMatrix B'
  let Q0 : Matrix n n K := B'.toMatrix (Pi.basisFun K n)
  have hPQ : P0 * Q0 = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hQP : Q0 * P0 = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  let P : Matrix.GeneralLinearGroup n K := ⟨P0, Q0, hPQ, hQP⟩
  refine ⟨P, e, fun a => ?_⟩
  have hcol : E a * P0 = P0 * Matrix.diagonal fun i => if e i = a then 1 else 0 := by
    ext r i
    rw [Matrix.mul_diagonal]
    have h := congrFun (hEW a (e i) (B' i) (hB' i)) r
    have hP : ∀ r', P0 r' i = B' i r' := fun r' => by
      simp [P0, Basis.toMatrix_apply]
    rw [Matrix.mul_apply]
    simp only [hP]
    change (E a).mulVec (B' i) r = _ at h
    rw [Matrix.mulVec] at h
    change (∑ x, E a r x * B' i x) = _ at h
    rw [h]
    by_cases hai : a = e i
    · simp [hai]
    · simp [hai, Ne.symm hai]
  change Q0 * E a * P0 = _
  rw [Matrix.mul_assoc, hcol, ← Matrix.mul_assoc, hQP, Matrix.one_mul]

end Langlands.LinearAlgebra
