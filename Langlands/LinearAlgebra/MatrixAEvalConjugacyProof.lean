import Langlands.LinearAlgebra.MatrixAEvalConjugacyStatement

namespace Langlands

universe uK

/-- Polynomial-module isomorphisms intertwine the underlying matrices. -/
theorem matrixAEvalConjugacy : MatrixAEvalConjugacyStatement.{uK} := by
  intro K _ n x y e
  let f : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (Module.AEval'.of x.mulVecLin).trans
      ((e.restrictScalars K).trans (Module.AEval'.of y.mulVecLin).symm)
  have hf (v : Fin n → K) : f (x.mulVecLin v) = y.mulVecLin (f v) := by
    change (Module.AEval'.of y.mulVecLin).symm
      (e (Module.AEval'.of x.mulVecLin (x.mulVecLin v))) = _
    rw [← Module.AEval'.X_smul_of, e.map_smul, Module.AEval'.of_symm_X_smul]
    rfl
  let g : Matrix.GeneralLinearGroup (Fin n) K :=
    { val := LinearMap.toMatrix' f.toLinearMap
      inv := LinearMap.toMatrix' f.symm.toLinearMap
      val_inv := by
        rw [← LinearMap.toMatrix'_comp]
        simp
      inv_val := by
        rw [← LinearMap.toMatrix'_comp]
        simp }
  have hg : (g : Matrix (Fin n) (Fin n) K) * x = y * g := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simpa [Matrix.toLin'_mul, g] using hf v
  refine ⟨g, ?_⟩
  rw [hg, mul_assoc, g.mul_inv, mul_one]

end Langlands
