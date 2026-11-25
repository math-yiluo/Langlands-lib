/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Central.Matrix

/-!
# Centrality of the entries of a central matrix algebra

If `Matrix (Fin n) (Fin n) D` is isomorphic to a central `K`-algebra and `n ≠ 0`, then `D` is
central over `K`.
-/

@[expose] public section

namespace Algebra.IsCentral

/-- If `A ≃ₐ[K] Matrix (Fin n) (Fin n) D` with `A` central over `K` and `n ≠ 0`, then `D` is
central over `K`. -/
theorem of_algEquiv_matrix {K A D : Type*} [CommSemiring K] [Semiring A] [Algebra K A]
    [Algebra.IsCentral K A] [Semiring D] [Algebra K D] {n : ℕ} [NeZero n]
    (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) D) : Algebra.IsCentral K D where
  out a ha := by
    have hscalar :
        Matrix.scalarAlgHom (Fin n) K a ∈ Subalgebra.center K (Matrix (Fin n) (Fin n) D) := by
      rw [Matrix.subalgebraCenter_eq_scalarAlgHom_map]
      exact Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩
    have hmem : e.symm (Matrix.scalarAlgHom (Fin n) K a) ∈ Subalgebra.center K A := by
      rw [Subalgebra.mem_center_iff]
      intro z
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact Subalgebra.mem_center_iff.mp hscalar (e z)
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hmem)
    refine Algebra.mem_bot.mpr ⟨c, ?_⟩
    have := congrFun (congrFun (congrArg e hc) 0) 0
    simpa [Matrix.algebraMap_matrix_apply] using this

end Algebra.IsCentral
