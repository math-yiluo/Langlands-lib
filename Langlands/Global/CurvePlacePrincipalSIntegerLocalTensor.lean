import Langlands.Global.CurvePlacePrincipalSIntegerFinite
import Langlands.Global.DedekindValuationOverring
import Langlands.Global.IntegralClosureLocalizationTensor
import Langlands.Global.CurvePlaceIntegralTensor

noncomputable section

universe u

open IsDedekindDomain IntermediateField AlgebraicCurve
open scoped TensorProduct AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension
  Langlands.Global.CurvePlaceIntegralClosure Langlands.Global.CurvePlaceIntegralTensor

namespace Langlands.Global.CurvePlacePrincipalSIntegerLocalTensor

variable (k K : Type u) [Field k] [Finite k] [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  (s : K) [FiniteDimensional k⟮s⟯ K] (t : CurveModel.chartRing k ({s} : Set K))
  [Fact (t ≠ 0)] (p : Place k K)
  [Fact (p ∉ curvePlacePrincipalExceptional k K s (t : K))]

/-- The actual lower S-integer inclusion in an original local ring outside the exceptional set. -/
def lowerMap :
    curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)) →+*
      p.toValuationSubring :=
  (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))).subtype.codRestrict _
    fun a => a.property p Fact.out

scoped instance lowerAlgebra : Algebra
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
    p.toValuationSubring :=
  (lowerMap k K s t p).toAlgebra

scoped instance originalFieldTower : IsScalarTower
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
    p.toValuationSubring K := .of_algebraMap_eq fun _ => rfl

/-- The original lower place has an actual nonzero center on the original global S-integer ring. -/
def centerPrime : HeightOneSpectrum
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) :=
  DedekindValuationOverring.prime
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
    K p.toValuationSubring p.ne_top'

scoped instance localization : IsLocalization
    (centerPrime k K s t p).asIdeal.primeCompl p.toValuationSubring :=
  DedekindValuationOverring.isLocalization
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
    K p.toValuationSubring p.ne_top'

scoped instance completedAlgebra : Algebra
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
    (curvePlaceCompletionIntegers p) :=
  ((curvePlaceIntegersMap p).comp (lowerMap k K s t p)).toAlgebra

scoped instance completedTower : IsScalarTower
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
    p.toValuationSubring (curvePlaceCompletionIntegers p) :=
  .of_algebraMap_eq fun _ => rfl

variable (L : Type u) [Field L] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L]

scoped instance upperFieldTower : IsScalarTower
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
    p.toValuationSubring L := .of_algebraMap_eq fun _ => rfl

/-- Localizing the actual upper S-integers gives the original lower-place integral closure. -/
def localTensorEquiv :
    p.toValuationSubring ⊗[
      curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))]
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) ≃ₐ[p.toValuationSubring]
      curvePlaceIntegralClosure L p :=
  integralClosureLocalizationTensorEquiv
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
    p.toValuationSubring _ L (centerPrime k K s t p).asIdeal.primeCompl

@[simp]
theorem localTensorEquiv_tmul (a : p.toValuationSubring)
    (b : curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) :
    (localTensorEquiv k K s t p L
      (a ⊗ₜ[curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))] b) : L) =
      algebraMap K L (a : K) * (b : L) :=
  integralClosureLocalizationTensorEquiv_tmul
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
    p.toValuationSubring _ L (centerPrime k K s t p).asIdeal.primeCompl a b

/-- The actual completed-integer tensor of the original global S-integer coefficients. -/
def completedTensorEquiv :
    curvePlaceCompletionIntegers p ⊗[
      curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))]
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) ≃ₐ[curvePlaceCompletionIntegers p]
      (∀ q : CurvePlacesAbove k L p, curvePlaceCompletionIntegers q.1) :=
  (((Algebra.TensorProduct.cancelBaseChange
      (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      p.toValuationSubring (curvePlaceCompletionIntegers p) (curvePlaceCompletionIntegers p)
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))))).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl
      (R := curvePlaceCompletionIntegers p) (A₁ := curvePlaceCompletionIntegers p))
      (localTensorEquiv k K s t p L))).trans
    (CurvePlaceIntegralTensor.integralTensorEquiv (L := L) p))

/-- The comparison retains the original completed embedding and every original upper coefficient. -/
@[simp]
theorem completedTensorEquiv_tmul (a : curvePlaceCompletionIntegers p)
    (b : curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (q : CurvePlacesAbove k L p) :
    (completedTensorEquiv k K s t p L
      (a ⊗ₜ[curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))] b) q :
        curvePlaceCompletion q.1) =
      CurvePlaceCompletionExtension.completionMap p q a *
        algebraMap L (curvePlaceCompletion q.1) (b : L) := by
  simp only [completedTensorEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, CurvePlaceIntegralTensor.integralTensorEquiv_tmul]
  change CurvePlaceCompletionExtension.completionMap p q a *
    algebraMap L (curvePlaceCompletion q.1)
      (localTensorEquiv k K s t p L
        (1 ⊗ₜ[curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))] b) : L) = _
  simp only [localTensorEquiv_tmul, OneMemClass.coe_one, map_one, one_mul]

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- Every original upper place above this lower place lies outside the full exceptional preimage. -/
theorem upper_notMem (q : CurvePlacesAbove k L p) :
    q.1 ∉ curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)) := by
  rw [mem_curvePlaceExceptionalPreimage,
    (curvePlaceRestriction_eq_iff q.1 p).mpr q.2]
  exact Fact.out

/-- Include the actual upper global coefficients in each original completed upper integer ring. -/
def upperMap (q : CurvePlacesAbove k L p) :
    curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K))) →+*
      curvePlaceCompletionIntegers q.1 :=
  (curvePlaceIntegersMap q.1).comp
    ((curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))).subtype.codRestrict _
      fun b => b.property q.1 (upper_notMem k K s t p L q))

scoped instance upperCompletedAlgebra (q : CurvePlacesAbove k L p) :
    Algebra
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))))
      (curvePlaceCompletionIntegers q.1) :=
  (upperMap k K s t p L q).toAlgebra

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
@[simp]
theorem upperMap_coe
    (b : curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (q : CurvePlacesAbove k L p) :
    (upperMap k K s t p L q b : curvePlaceCompletion q.1) =
      algebraMap L (curvePlaceCompletion q.1) (b : L) := rfl

/-- The right tensor coefficient is exactly the original upper integral coefficient map. -/
@[simp]
theorem completedTensorEquiv_one_tmul
    (b : curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (q : CurvePlacesAbove k L p) :
    completedTensorEquiv k K s t p L
      (1 ⊗ₜ[curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))] b) q =
        algebraMap
          (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K))))
          (curvePlaceCompletionIntegers q.1) b := by
  apply Subtype.ext
  simp only [completedTensorEquiv_tmul, OneMemClass.coe_one, map_one, one_mul]
  rfl

end Langlands.Global.CurvePlacePrincipalSIntegerLocalTensor
