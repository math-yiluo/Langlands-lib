import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Langlands.Algebra.ReducedCharpoly

/-! # Reduced Cayley–Hamilton and quadratic coefficients in a division algebra -/

noncomputable section

universe u

open Polynomial
open scoped TensorProduct

namespace Langlands.CentralDivision

open Langlands.CentralSimple

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- The actual reduced characteristic polynomial annihilates an original division element. -/
theorem aeval_reducedCharpoly (a : D) :
    Polynomial.aeval a (reducedCharpoly K D a) = 0 := by
  have h := Algebra.aeval_self_charpoly_lmul (R := K) a
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis K D)] at h
  change Polynomial.aeval a (Algebra.leftMulMatrix (Module.finBasis K D) a).charpoly = 0 at h
  rw [charpoly_leftMulMatrix_eq_reducedCharpoly_pow, map_pow] at h
  exact eq_zero_of_pow_eq_zero h

end Langlands.CentralDivision

namespace Langlands.CentralSimple

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- In reduced degree two the constant coefficient is the reduced norm. -/
theorem reducedCharpoly_coeff_zero_two (hdegree : reducedDegree K D = 2) (a : D) :
    (reducedCharpoly K D a).coeff 0 =
      reducedNorm K D K (1 ⊗ₜ[K] a) := by
  rw [Polynomial.coeff_zero_eq_eval_zero, reducedCharpoly_eval]
  have heq : (0 : K) ⊗ₜ[K] (1 : D) - (1 : K) ⊗ₜ[K] a =
      ((-1 : K) ⊗ₜ[K] (1 : D)) * ((1 : K) ⊗ₜ[K] a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp [TensorProduct.neg_tmul]
  rw [heq, map_mul, reducedNorm_scalar, hdegree]
  simp

/-- The explicit quadratic expansion of the reduced characteristic polynomial. -/
theorem reducedCharpoly_eq_quadratic (hdegree : reducedDegree K D = 2) (a : D) :
    reducedCharpoly K D a = X ^ 2 + C ((reducedCharpoly K D a).coeff 1) * X +
      C (reducedNorm K D K (1 ⊗ₜ[K] a)) := by
  have hn := reducedCharpoly_natDegree K D a
  rw [hdegree] at hn
  have hc : (reducedCharpoly K D a).coeff 2 = 1 := by
    simpa only [hn] using (reducedCharpoly_monic K D a).coeff_natDegree
  have h := (reducedCharpoly K D a).as_sum_range_C_mul_X_pow
  rw [hn] at h
  simpa [Finset.sum_range_succ, hc, reducedCharpoly_coeff_zero_two K D hdegree a,
    add_comm, add_left_comm, add_assoc] using h

end Langlands.CentralSimple
