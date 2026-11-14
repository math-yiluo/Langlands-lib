import Langlands.GroupScheme.Torus.FiniteAlgebraWeightIdempotents
import Mathlib.Algebra.DirectSum.Module

/-! # Division-algebra row spaces of universal split-torus weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix TensorProduct DirectSum

namespace Langlands.GroupScheme.FiniteMatrixAlgebraTorusWeights

set_option backward.isDefEq.respectTransparency false

open FiniteAlgebraUnits FiniteAlgebraTorusWeights SplitTorusRepresentationWeights

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  {n : Type} [Fintype n] [DecidableEq n]
  {d : ℕ} {b : Module.Basis (Fin d) K (Matrix n n D)}
  {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ groupScheme b)

/-- The row projection obtained by right multiplication by a universal weight idempotent. -/
def rowWeightProjection (m : I → ℤ) : Module.End D (n → D) :=
  (weightElement i m).toLinearMapRight'

/-- Rows fixed by the universal idempotent for exponent `m`. -/
def rowWeightSpace (m : I → ℤ) : Submodule D (n → D) where
  carrier := {v | rowWeightProjection i m v = v}
  zero_mem' := map_zero _
  add_mem' {v w} hv hw := by
    change rowWeightProjection i m (v + w) = v + w
    rw [map_add, hv, hw]
  smul_mem' a v hv := by
    change rowWeightProjection i m (a • v) = a • v
    rw [map_smul, hv]

theorem mem_rowWeightSpace (m : I → ℤ) (v : n → D) :
    v ∈ rowWeightSpace i m ↔ v ᵥ* weightElement i m = v := Iff.rfl

/-- Every projected row lies in the corresponding weight space. -/
theorem rowWeightProjection_mem (m : I → ℤ) (v : n → D) :
    rowWeightProjection i m v ∈ rowWeightSpace i m := by
  change (v ᵥ* weightElement i m) ᵥ* weightElement i m = v ᵥ* weightElement i m
  rw [Matrix.vecMul_vecMul, weightElement_mul, ite_eq_left rfl]

/-- Weight projections isolate the weight spaces. -/
theorem rowWeightProjection_of_mem (m p : I → ℤ) {v : n → D}
    (hv : v ∈ rowWeightSpace i p) :
    rowWeightProjection i m v = if p = m then v else 0 := by
  change v ᵥ* weightElement i m = _
  rw [← (mem_rowWeightSpace i p v).mp hv, Matrix.vecMul_vecMul, weightElement_mul]
  split_ifs with h
  · rfl
  · exact Matrix.vecMul_zero _

/-- The row weight spaces span the entire left division-algebra module. -/
theorem iSup_rowWeightSpace_eq_top : (⨆ m : I → ℤ, rowWeightSpace i m) = ⊤ := by
  classical
  apply top_unique
  intro v _
  have hsum : (∑ m ∈ weightSupport (rightRegularRepresentation b) I i,
      rowWeightProjection i m v) = v := by
    change (∑ m ∈ weightSupport (rightRegularRepresentation b) I i,
      v ᵥ* weightElement i m) = v
    rw [← Matrix.vecMul_sum, sum_weightElement, Matrix.vecMul_one]
  rw [← hsum]
  exact Submodule.sum_mem _ (fun m _ =>
    Submodule.mem_iSup_of_mem m (rowWeightProjection_mem i m v))

/-- Distinct row weight spaces are independent over the division algebra. -/
theorem rowWeightSpace_iSupIndep : iSupIndep (rowWeightSpace i) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum m hm
  have h : (∑ p ∈ s, rowWeightProjection i m (v p)) = 0 := by
    rw [← map_sum, hsum, map_zero]
  have he : (∑ p ∈ s, rowWeightProjection i m (v p)) = v m := by
    calc
      _ = ∑ p ∈ s, if p = m then v p else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact rowWeightProjection_of_mem i m p (hv p hp)
      _ = v m := by simp [hm]
  exact he.symm.trans h

/-- The row module is the internal direct sum of its universal torus weight spaces. -/
theorem rowWeightSpace_isInternal : DirectSum.IsInternal (rowWeightSpace i) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (rowWeightSpace_iSupIndep i) (iSup_rowWeightSpace_eq_top i)

/-- Canonical decomposition into the finitely supported family of row weights. -/
def rowWeightDecomposition : (n → D) ≃ₗ[D] ⨁ m : I → ℤ, rowWeightSpace i m :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (rowWeightSpace i))
    (rowWeightSpace_isInternal i)).symm

/-- The row space of an exponent outside the regular weight support vanishes. -/
theorem rowWeightSpace_eq_bot {m : I → ℤ}
    (hm : m ∉ weightSupport (rightRegularRepresentation b) I i) :
    rowWeightSpace i m = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  have h := (mem_rowWeightSpace i m v).mp hv
  rw [weightElement_eq_zero i hm, Matrix.vecMul_zero] at h
  exact h.symm

/-- Every nonzero universal idempotent has a nonzero row weight space. -/
theorem rowWeightSpace_ne_bot {m : I → ℤ}
    (hm : m ∈ weightSupport (rightRegularRepresentation b) I i) :
    rowWeightSpace i m ≠ ⊥ := by
  intro hbot
  apply weightElement_ne_zero i hm
  funext r
  have hr : weightElement i m r ∈ rowWeightSpace i m := by
    change (weightElement i m r) ᵥ* weightElement i m = weightElement i m r
    funext c
    have h := congrFun (congrFun (weightElement_mul i m m) r) c
    simpa only [ite_true, Matrix.mul_apply, Matrix.vecMul, dotProduct] using h
  rw [hbot] at hr
  exact hr

/-- The support of the row grading is exactly that of the inverse-right regular representation. -/
theorem rowWeightSpace_ne_bot_iff (m : I → ℤ) :
    rowWeightSpace i m ≠ ⊥ ↔ m ∈ weightSupport (rightRegularRepresentation b) I i := by
  constructor
  · exact fun h => by_contra (fun hm => h (rowWeightSpace_eq_bot i hm))
  · exact rowWeightSpace_ne_bot i

end Langlands.GroupScheme.FiniteMatrixAlgebraTorusWeights
