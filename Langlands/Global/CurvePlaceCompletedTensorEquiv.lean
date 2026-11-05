import Langlands.Global.CurvePlaceIntegralPrimes

/-! # The completed-tensor decomposition at every actual function-field place -/

noncomputable section

universe u

open IsDedekindDomain
open scoped TensorProduct Langlands.Global.CurvePlaceCompletionExtension

namespace Langlands.Global.CurvePlaceCompletedTensorEquiv

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  [FiniteDimensional K L] [Finite k]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [IsScalarTower k K L]
  (p : AlgebraicCurve.Place k K)

/-- The sum of all actual completed local degrees is the original global degree. -/
theorem allLocalDegree_sum :
    (∑ q : CurvePlacesAbove k L p,
      Module.finrank (curvePlaceCompletion p) (curvePlaceCompletion q.1)) =
      Module.finrank K L := by
  apply le_antisymm (CurvePlaceCompletedProduct.allLocalDegree_sum_le p)
  rw [← CurvePlaceIntegralPrimes.sum_ramification_inertia (L := L) p]
  exact Finset.sum_le_sum fun q _ => CurvePlaceCompletedIntegersExtension.localDegree_lowerBound p q

/-- Each original ramification-inertia product equals its actual completed field degree. -/
theorem localDegree_eq (q : CurvePlacesAbove k L p) :
    Module.finrank (curvePlaceCompletion p) (curvePlaceCompletion q.1) =
      q.1.heightOneSpectrum.asIdeal.ramificationIdx p.toValuationSubring *
        q.1.heightOneSpectrum.asIdeal.inertiaDeg p.toValuationSubring := by
  have hs : (∑ q : CurvePlacesAbove k L p,
      q.1.heightOneSpectrum.asIdeal.ramificationIdx p.toValuationSubring *
        q.1.heightOneSpectrum.asIdeal.inertiaDeg p.toValuationSubring) =
      ∑ q : CurvePlacesAbove k L p,
        Module.finrank (curvePlaceCompletion p) (curvePlaceCompletion q.1) :=
    (CurvePlaceIntegralPrimes.sum_ramification_inertia p).trans (allLocalDegree_sum p).symm
  exact ((Finset.sum_eq_sum_iff_of_le
    (fun q _ => CurvePlaceCompletedIntegersExtension.localDegree_lowerBound p q)).mp hs
    q (Finset.mem_univ q)).symm

/-- The original simultaneous tensor map is bijective, with no separability premise. -/
theorem allTensorMap_bijective :
    Function.Bijective (CurvePlaceCompletedProduct.allTensorMap (L := L) p) := by
  let : Module.Free (curvePlaceCompletion p)
      (∀ q : CurvePlacesAbove k L p, curvePlaceCompletion q.1) :=
    Module.Free.of_divisionRing _ _
  let : ∀ q : CurvePlacesAbove k L p,
      Module.Free (curvePlaceCompletion p) (curvePlaceCompletion q.1) :=
    fun _ => Module.Free.of_divisionRing _ _
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    (CurvePlaceCompletedProduct.allTensorMap (L := L) p).toLinearMap
    (CurvePlaceCompletedProduct.allTensorMap_surjective p)
  rw [Module.finrank_baseChange, Module.finrank_pi_fintype, allLocalDegree_sum p]

/-- The canonical tensor decomposition uses every actual upper curve-place completion. -/
def allTensorEquiv :
    curvePlaceCompletion p ⊗[K] L ≃ₐ[curvePlaceCompletion p]
      (∀ q : CurvePlacesAbove k L p, curvePlaceCompletion q.1) :=
  AlgEquiv.ofBijective (CurvePlaceCompletedProduct.allTensorMap p) (allTensorMap_bijective p)

@[simp]
theorem allTensorEquiv_tmul (a : curvePlaceCompletion p) (x : L)
    (q : CurvePlacesAbove k L p) :
    allTensorEquiv p (a ⊗ₜ[K] x) q =
      CurvePlaceCompletionExtension.completionMap p q a *
        algebraMap L (curvePlaceCompletion q.1) x := rfl

@[simp]
theorem allTensorEquiv_one_tmul (x : L) (q : CurvePlacesAbove k L p) :
    allTensorEquiv p (1 ⊗ₜ[K] x) q = algebraMap L (curvePlaceCompletion q.1) x := by
  simp [allTensorEquiv_tmul]

end Langlands.Global.CurvePlaceCompletedTensorEquiv
