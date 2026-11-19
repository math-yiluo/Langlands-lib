import Langlands.Algebra.BrauerSplitting
import Langlands.Algebra.CentralDivisionTensorCubeProof

/-! # The triple Brauer class of a degree-six division algebra -/

noncomputable section

universe u

namespace Langlands.Brauer

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- A finite-dimensional central division algebra as an actual CSA. -/
def divisionAlgebra : CSA.{u, u} K where
  toAlgCat := AlgCat.of K D

/-- The triple Brauer class of a degree-six central division algebra is nonzero. -/
theorem three_zsmul_classOf_divisionAlgebra_ne_zero
    (hdegree : CentralSimple.reducedDegree K D = 6) :
    (3 : ℤ) • classOf (divisionAlgebra K D) ≠ 0 := by
  intro h
  let A := divisionAlgebra K D
  have hdim : Module.finrank K D = 36 := by
    rw [CentralSimple.finrank_eq_reducedDegree_mul_self, hdegree]
  have hsum : classOf (tensor (tensor A A) A) = 0 := by
    rw [show (3 : ℤ) = 1 + 1 + 1 by decide, add_zsmul, add_zsmul, one_zsmul] at h
    simpa only [classOf_tensor] using h
  obtain ⟨n, hn, he⟩ := (classOf_eq_zero_iff _).mp hsum
  exact CentralSimple.centralDivisionDegreeSixTensorCubeNonSplit K D hdim n hn he

end Langlands.Brauer
