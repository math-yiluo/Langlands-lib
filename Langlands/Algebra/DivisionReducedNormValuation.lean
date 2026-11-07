import Langlands.Algebra.DivisionNormValuation
import Langlands.Algebra.ReducedNormRegular
import Mathlib.RingTheory.SimpleRing.DivisionRing

/-! Valuations from the canonical reduced norm on a central division algebra. -/

noncomputable section

namespace Langlands.CentralDivision

open scoped TensorProduct
open Langlands.CentralSimple

universe u

section Algebraic

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- The regular norm on the original algebra is the reduced-degree power of its canonical norm. -/
theorem regularNorm_eq_reducedNorm_pow (x : D) :
    Algebra.norm K x = reducedNorm K D K (1 ⊗ₜ[K] x) ^ reducedDegree K D := by
  calc
    Algebra.norm K x = Algebra.norm K (1 ⊗ₜ[K] x) := by
      simpa only [Algebra.TensorProduct.lid_tmul, one_smul] using
        Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.lid K D) (1 ⊗ₜ[K] x)
    _ = _ := norm_eq_reducedNorm_pow K D K _

end Algebraic

section Normed

variable (K D : Type u) [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- The canonical reduced norm followed by the base norm is ultrametric on the original algebra. -/
theorem norm_reducedNorm_add_le (x y : D) :
    ‖reducedNorm K D K (1 ⊗ₜ[K] (x + y))‖ ≤
      max ‖reducedNorm K D K (1 ⊗ₜ[K] x)‖ ‖reducedNorm K D K (1 ⊗ₜ[K] y)‖ := by
  apply (pow_le_pow_iff_left₀ (norm_nonneg _)
    (le_trans (norm_nonneg _) (le_max_left _ _)) (reducedDegree_pos K D).ne').mp
  calc
    ‖reducedNorm K D K (1 ⊗ₜ[K] (x + y))‖ ^ reducedDegree K D =
        ‖Algebra.norm K (x + y)‖ := by
      rw [regularNorm_eq_reducedNorm_pow, norm_pow]
    _ ≤ max ‖Algebra.norm K x‖ ‖Algebra.norm K y‖ :=
      norm_regularNorm_add_le K D x y
    _ = (max ‖reducedNorm K D K (1 ⊗ₜ[K] x)‖
        ‖reducedNorm K D K (1 ⊗ₜ[K] y)‖) ^ reducedDegree K D := by
      rw [regularNorm_eq_reducedNorm_pow, regularNorm_eq_reducedNorm_pow, norm_pow, norm_pow]
      symm
      simpa only [Real.rpow_natCast] using Real.rpow_max (norm_nonneg _) (norm_nonneg _)
        (Nat.cast_nonneg (reducedDegree K D) : (0 : ℝ) ≤ _)

/-- The canonical reduced norm gives an actual valuation on the original central division algebra. -/
def reducedNormValuation : Valuation D NNReal where
  toFun x := ‖reducedNorm K D K (1 ⊗ₜ[K] x)‖₊
  map_zero' := by simp
  map_one' := by
    simp only [← Algebra.TensorProduct.includeRight_apply, map_one, nnnorm_one]
  map_mul' x y := by
    simp only [← Algebra.TensorProduct.includeRight_apply, map_mul, nnnorm_mul]
  map_add_le_max' x y := by
    exact_mod_cast norm_reducedNorm_add_le K D x y

@[simp]
theorem reducedNormValuation_algebraMap (a : K) :
    reducedNormValuation K D (algebraMap K D a) = ‖a‖₊ ^ reducedDegree K D := by
  change ‖reducedNorm K D K (1 ⊗ₜ[K] algebraMap K D a)‖₊ = _
  rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]
  simp only [Algebra.algebraMap_self_apply, reducedNorm_scalar, nnnorm_pow]

/-- The regular and canonical reduced norm valuations differ by the reduced-degree power. -/
theorem regularNormValuation_eq_reducedNormValuation_pow (x : D) :
    regularNormValuation K D x = reducedNormValuation K D x ^ reducedDegree K D := by
  change ‖Algebra.norm K x‖₊ = _
  rw [regularNorm_eq_reducedNorm_pow, nnnorm_pow]
  rfl

end Normed

end Langlands.CentralDivision
