/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The characteristic polynomial of an endomorphism of a direct sum

If an endomorphism `f` of `M` preserves every summand of an internal direct sum decomposition
`M = ⨁ i, N i`, its matrix in a basis adapted to the decomposition is block diagonal, so its
characteristic polynomial is the product of the characteristic polynomials of the restrictions
`f ∣ N i`. This is the characteristic-polynomial analogue of
`LinearMap.trace_eq_sum_trace_restrict`.

## Main statements

- `LinearMap.charpoly_eq_prod_charpoly_restrict`
-/

@[expose] public section

open DirectSum Module Set

namespace LinearMap

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {N : ι → Submodule R M}
  [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]

/-- The characteristic polynomial of an endomorphism of a direct sum which preserves every
summand is the product of the characteristic polynomials of the restrictions to the summands.

The linear order on `ι` is only used to see the block diagonal matrix of `f` as block
triangular. -/
theorem charpoly_eq_prod_charpoly_restrict [Module.Free R M] [Module.Finite R M] [Fintype ι]
    [LinearOrder ι] (h : IsInternal N) {f : M →ₗ[R] M} (hf : ∀ i, MapsTo f (N i) (N i)) :
    f.charpoly = ∏ i, (f.restrict (hf i)).charpoly := by
  classical
  let b : (i : ι) → Basis _ R (N i) := fun i ↦ Module.Free.chooseBasis R (N i)
  rw [← charpoly_toMatrix f (h.collectedBasis b),
    toMatrix_directSum_collectedBasis_eq_blockDiagonal' h h b b hf,
    (Matrix.blockTriangular_blockDiagonal' _).charpoly]
  have hblock (a : ι) : ((Matrix.blockDiagonal' fun i ↦
      toMatrix (b i) (b i) (f.restrict (hf i))).toSquareBlock Sigma.fst a).charpoly =
      (f.restrict (hf a)).charpoly := by
    have he : (Matrix.blockDiagonal' fun i ↦
        toMatrix (b i) (b i) (f.restrict (hf i))).toSquareBlock Sigma.fst a =
        Matrix.reindex (Equiv.sigmaSubtype a).symm (Equiv.sigmaSubtype a).symm
          (toMatrix (b a) (b a) (f.restrict (hf a))) := by
      ext x y
      obtain ⟨⟨i, c⟩, rfl⟩ := x
      obtain ⟨⟨j, d⟩, hj⟩ := y
      dsimp only at hj
      subst hj
      simp [Matrix.toSquareBlock_def, Matrix.blockDiagonal'_apply_eq]
    rw [he, Matrix.charpoly_reindex, charpoly_toMatrix]
  refine (Finset.prod_congr rfl fun a _ ↦ hblock a).trans ?_
  refine Finset.prod_subset (Finset.subset_univ _) fun a _ ha ↦ ?_
  have : IsEmpty (Module.Free.ChooseBasisIndex R (N a)) :=
    ⟨fun c ↦ ha (Finset.mem_image.mpr ⟨⟨a, c⟩, Finset.mem_univ _, rfl⟩)⟩
  rw [← charpoly_toMatrix (f.restrict (hf a)) (b a), Matrix.charpoly_isEmpty]

end LinearMap
