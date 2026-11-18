import Langlands.Algebra.SylowTwoOddSplitting
import Langlands.Algebra.CentralSimple.FiniteGaloisSplitting
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Actual tensor cubes of degree-six division algebras do not split -/

noncomputable section
universe u
open Matrix
open scoped TensorProduct

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CentralSimple

variable {k D : Type u} [Field k] [DivisionRing D] [Algebra k D]
  [FiniteDimensional k D] [Algebra.IsCentral k D]

omit [Algebra.IsCentral k D] in
/-- An actual matrix presentation of the tensor cube has the unique required
size and can be reindexed by the actual threefold product index. -/
theorem tensorCube_split_product_index (hdim : Module.finrank k D = 36) {m : ℕ}
    (f : (D ⊗[k] D) ⊗[k] D ≃ₐ[k] Matrix (Fin m) (Fin m) k) :
    Nonempty ((D ⊗[k] D) ⊗[k] D ≃ₐ[k]
      Matrix ((Fin 6 × Fin 6) × Fin 6) ((Fin 6 × Fin 6) × Fin 6) k) := by
  have hsize : 46656 = m * m := by
    have h := f.toLinearEquiv.finrank_eq
    simpa only [Module.finrank_tensorProduct, hdim, Module.finrank_matrix,
      Fintype.card_fin, Module.finrank_self, mul_one] using h
  have hm : m = 216 := by nlinarith
  let q : Fin m ≃ ((Fin 6 × Fin 6) × Fin 6) :=
    Fintype.equivOfCardEq (by simp [hm])
  exact ⟨f.trans (Matrix.reindexAlgEquiv k k q)⟩

/-- Over every field, the actual tensor cube of a central division algebra of
dimension thirty-six has no matrix-algebra splitting. -/
theorem centralDivision_degree_six_tensorCube_not_split
    (hdim : Module.finrank k D = 36) (m : ℕ) :
    ¬ Nonempty ((D ⊗[k] D) ⊗[k] D ≃ₐ[k] Matrix (Fin m) (Fin m) k) := by
  rintro ⟨f⟩
  let L := finiteGaloisSplittingField k D
  have hdegree : reducedDegree k D = 6 := by
    have h := (finiteGaloisSplittingChart_spec k D).2
    rw [hdim] at h
    nlinarith
  let e : L ⊗[k] D ≃ₐ[L] Matrix (Fin 6) (Fin 6) L :=
    (finiteGaloisSplittingChart k D).trans
      (Matrix.reindexAlgEquiv L L (finCongr hdegree))
  obtain ⟨f₃⟩ := tensorCube_split_product_index hdim f
  have hcube := splittingChart_scalarDefect_cube_isCoboundary_of_tensorCube_split e f₃
  rw [splittingChartIndexAction_fin_eq] at hcube
  exact division_degree_six_scalarDefect_cube_not_coboundary hdim e hcube

end Langlands.CentralSimple
