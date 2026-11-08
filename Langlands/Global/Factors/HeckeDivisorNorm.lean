import Langlands.Global.Factors.HeckeDivisor
import Langlands.Global.IdeleAbsoluteValue

/-! # Norm of the finite divisor of an actual idele -/

noncomputable section

universe u

namespace Langlands.Global.HeckeDivisor

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.ClassField.Global
open Langlands.Global.CompletionPadic
open scoped NumberField NNReal

variable {K : Type u} [Field K] [NumberField K]

/-- The existing divisor restricted to finite ideles by their actual inclusion. -/
def finiteDivisor (x : FiniteIdeles K) : FinitePlaceDivisor K :=
  ideleDivisor (finiteIdelesInclusion K x)

@[simp] theorem finiteDivisor_one : finiteDivisor (1 : FiniteIdeles K) = 0 := by
  simp [finiteDivisor]

@[simp] theorem finiteDivisor_mul (x y : FiniteIdeles K) :
    finiteDivisor (x * y) = finiteDivisor x + finiteDivisor y := by
  simp [finiteDivisor]

/-- The completion norm uses exactly the residue norm and actual local shell order. -/
theorem local_norm_eq (v : FinitePlace K) (x : (FiniteCompletion K v)ˣ) :
    ‖(x : FiniteCompletion K v)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-(topologicalData v).ord
        (x : FiniteCompletion K v)) := by
  rw [ord_eq_neg_unitsExponent, neg_neg, FinitePlace.norm_def, valued_units,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp only [WithZero.exp, WithZero.unzero_coe, NNReal.coe_zpow, NNReal.coe_natCast]
  rfl

theorem norm_pos (d : FinitePlaceDivisor K) : 0 < norm d := by
  classical
  apply Finset.prod_pos
  intro v _
  exact zpow_pos (lt_trans zero_lt_one (by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)) _

/-- The divisor product may be taken over all places, since its exponents have finite support. -/
theorem norm_eq_finprod (d : FinitePlaceDivisor K) :
    norm d = ∏ᶠ v : FinitePlace K, (Ideal.absNorm v.asIdeal : ℝ) ^ d v := by
  classical
  symm
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  by_contra hd
  have hd' : d v = 0 := Finsupp.notMem_support_iff.mp hd
  exact hv (by simp only [hd', zpow_zero])

/-- With orders positive on prime ideals, the divisor norm is inverse to the finite idelic norm. -/
theorem norm_ideleDivisor (x : Ideles K) :
    norm (ideleDivisor x) = (∏ᶠ v : FinitePlace K, ‖x.val.2 v‖)⁻¹ := by
  rw [norm_eq_finprod, ← finprod_inv_distrib]
  apply finprod_congr
  intro v
  rw [ideleDivisor_apply_eq_ord]
  have h := local_norm_eq v (ideleCoordinate v x)
  rw [ideleCoordinate_val] at h
  rw [h, ← zpow_neg, neg_neg, ideleCoordinate_val]

/-- Exact comparison with the already constructed normalized finite idelic absolute value. -/
theorem norm_finiteDivisor (x : FiniteIdeles K) :
    norm (finiteDivisor x) = ((IdeleAbsoluteValue.finite K x : ℝ≥0) : ℝ)⁻¹ := by
  rw [finiteDivisor, norm_ideleDivisor]
  rfl

/-- The full idelic absolute value splits into its infinite norm and the inverse divisor norm. -/
theorem full_eq_infinite_mul_norm_inv (x : Ideles K) :
    ((IdeleAbsoluteValue.full K x : ℝ≥0) : ℝ) =
      (∏ v : InfinitePlace K, ‖x.val.1 v‖ ^ v.mult) * (norm (ideleDivisor x))⁻¹ := by
  rw [IdeleAbsoluteValue.coe_full, norm_ideleDivisor, inv_inv]

end Langlands.Global.HeckeDivisor
