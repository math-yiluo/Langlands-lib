import Langlands.LinearAlgebra.FiniteRankTrace

/-! # Finite-rank transpose and restrictions containing the full image -/

noncomputable section

namespace Langlands.FiniteRankEnd

universe uV

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Restrict to a subspace containing the entire image, retaining finite rank. -/
def restrict (T : finiteRankEnd V) (S : Submodule ℂ V) (hS : T.val.range ≤ S) :
    finiteRankEnd S :=
  ofFactorization (T.val.rangeRestrict.comp S.subtype) (Submodule.inclusion hS)

@[simp]
theorem restrict_coe (T : finiteRankEnd V) (S : Submodule ℂ V)
    (hS : T.val.range ≤ S) :
    (restrict T S hS).val = onSubspace T.val S hS := rfl

@[simp]
theorem restrict_apply (T : finiteRankEnd V) (S : Submodule ℂ V)
    (hS : T.val.range ≤ S) (v : S) :
    ((restrict T S hS).val v : V) = T.val v := rfl

/-- An image-containing restriction has the original genuine finite-rank trace.
The containing subspace itself may be infinite-dimensional. -/
@[simp]
theorem trace_restrict (T : finiteRankEnd V) (S : Submodule ℂ V)
    (hS : T.val.range ≤ S) :
    trace (restrict T S hS) = trace T := by
  rw [restrict, trace_ofFactorization]
  rfl

/-- The actual algebraic transpose, factored through the dual of the finite image. -/
def transpose (T : finiteRankEnd V) : finiteRankEnd (Module.Dual ℂ V) :=
  ofFactorization T.val.range.subtype.dualMap T.val.rangeRestrict.dualMap

@[simp]
theorem transpose_coe (T : finiteRankEnd V) :
    (transpose T).val = T.val.dualMap := by
  ext ℓ v
  rfl

@[simp]
theorem transpose_apply (T : finiteRankEnd V) (ℓ : Module.Dual ℂ V) (v : V) :
    (transpose T).val ℓ v = ℓ (T.val v) := rfl

/-- Transpose preserves the genuine finite-rank trace on arbitrary carriers. -/
@[simp]
theorem trace_transpose (T : finiteRankEnd V) :
    trace (transpose T) = trace T := by
  rw [transpose, trace_ofFactorization]
  change LinearMap.trace ℂ (Module.Dual ℂ T.val.range)
      (Module.Dual.transpose (onSubspace T.val T.val.range le_rfl)) =
    LinearMap.trace ℂ T.val.range (onSubspace T.val T.val.range le_rfl)
  exact LinearMap.trace_transpose' _

/-- Restrict the actual transpose to a subspace containing its full image. -/
def transposeOn (T : finiteRankEnd V) (S : Submodule ℂ (Module.Dual ℂ V))
    (hS : T.val.dualMap.range ≤ S) : finiteRankEnd S :=
  restrict (transpose T) S (by simpa only [transpose_coe] using hS)

@[simp]
theorem transposeOn_coe (T : finiteRankEnd V)
    (S : Submodule ℂ (Module.Dual ℂ V)) (hS : T.val.dualMap.range ≤ S) :
    (transposeOn T S hS).val = onSubspace T.val.dualMap S hS := by
  ext ℓ v
  rfl

@[simp]
theorem transposeOn_apply (T : finiteRankEnd V)
    (S : Submodule ℂ (Module.Dual ℂ V)) (hS : T.val.dualMap.range ≤ S)
    (ℓ : S) (v : V) :
    ((transposeOn T S hS).val ℓ : Module.Dual ℂ V) v = ℓ.val (T.val v) := rfl

/-- Full-image containment allows the restricted transpose to compute the trace. -/
@[simp]
theorem trace_transposeOn (T : finiteRankEnd V)
    (S : Submodule ℂ (Module.Dual ℂ V)) (hS : T.val.dualMap.range ≤ S) :
    trace (transposeOn T S hS) = trace T := by
  rw [transposeOn, trace_restrict, trace_transpose]

end Langlands.FiniteRankEnd
