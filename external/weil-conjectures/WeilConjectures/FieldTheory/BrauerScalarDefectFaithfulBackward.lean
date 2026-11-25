/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.FieldTheory.BrauerScalarDefect
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.FieldTheory.CentralSimpleTensorEnd
import WeilConjectures.FieldTheory.BrauerScalarDefectTensorSplit
@[expose] public section
universe u
namespace Field
/-- Equal scalar-defect classes imply Brauer equivalence.

Equality in cohomology makes the quotient of the two matrix descent defects a
scalar coboundary.  Rescaling one lift by its scalar one-cochain gives a genuine
general-linear cocycle on a finite Galois extension.  Finite Galois descent (the
matrix form of Hilbert 90) trivializes this cocycle, so the tensor product of `A`
with the opposite of `B` is an endomorphism algebra.  The central-simple-algebra
criterion for a split tensor product then gives isomorphic positive matrix
amplifications of `A` and `B`, namely `IsBrauerEquivalent A B`.  This is the
injectivity argument in Stacks Project, Theorem 03R7; the cocycle convention is
that of Section 0DVG. (blueprint: lem-sc-brauer-scalar-defect-faithful-backward). -/
theorem brauerEquivalent_of_brauerScalarDefect_eq (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K B y)
    (h : x = y) : IsBrauerEquivalent A B := by
  classical
  obtain ⟨n, hn, ⟨eAB⟩⟩ := tensor_opposite_split_of_brauerScalarDefect_eq K A B x y hx hy h
  let m := Module.finrank K B
  have hm : m ≠ 0 := ne_of_gt (Module.finrank_pos (R := K) (M := B))
  let eBB : (TensorProduct K Bᵐᵒᵖ B) ≃ₐ[K] Matrix (Fin m) (Fin m) K :=
    (Algebra.TensorProduct.comm K Bᵐᵒᵖ B).trans
      ((AlgEquiv.ofBijective (AlgHom.mulLeftRight K B)
        (centralSimple_mulLeftRight_bijective K B)).trans
        (LinearMap.toMatrixAlgEquiv (Module.finBasis K B)))
  -- M_m(A) ≃ A ⊗ (Bᵐᵒᵖ ⊗ B) ≃ (A ⊗ Bᵐᵒᵖ) ⊗ B ≃ M_n(B).
  refine ⟨m, n, hm, hn, ⟨?_⟩⟩
  exact (matrixEquivTensor (Fin m) K A).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[K] A) eBB.symm).trans
      ((Algebra.TensorProduct.assoc K K K A Bᵐᵒᵖ B).symm.trans
        ((Algebra.TensorProduct.congr eAB (AlgEquiv.refl : B ≃ₐ[K] B)).trans
          ((Algebra.TensorProduct.comm K (Matrix (Fin n) (Fin n) K) B).trans
            (matrixEquivTensor (Fin n) K B).symm))))
end Field
