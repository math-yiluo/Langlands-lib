import Langlands.Global.NumberFieldSIntegerFinite
import Langlands.Global.NumberFieldPlaceIntegralTensor
import Langlands.Global.DedekindValuationOverring

noncomputable section

universe u

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.NumberFieldPlaceIntegralTensor
  Langlands.Global.AdelicFunctoriality.FiniteExtension
  Langlands.Global.AdelicFunctoriality.IntegralTensor

namespace Langlands.Global.NumberFieldSIntegerLocalTensor

variable (K : Type u) [Field K] [NumberField K]
  (S : Finset (FinitePlace K)) (p : FinitePlace K) [Fact (p ∉ S)]

omit [Fact (p ∉ S)] in
private theorem localRing_ne_top : NumberFieldPlaceIntegralTensor.localRing K p ≠ ⊤ := by
  rw [NumberFieldPlaceIntegralTensor.localRing, valuationSubringAtPrime_eq_valuationSubring]
  simpa only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not] using
    (inferInstance : (p.valuation K).IsNontrivial)

/-- The actual lower S-integer inclusion in an original local ring outside the exceptional set. -/
def lowerMap :
    ((S : Set (FinitePlace K)).integer K) →+*
      (NumberFieldPlaceIntegralTensor.localRing K p) :=
  (((S : Set (FinitePlace K)).integer K)).toSubring.subtype.codRestrict _
    fun a => by
      rw [NumberFieldPlaceIntegralTensor.localRing, valuationSubringAtPrime_eq_valuationSubring]
      exact a.property p Fact.out

scoped instance lowerAlgebra : Algebra
    (((S : Set (FinitePlace K)).integer K))
    (NumberFieldPlaceIntegralTensor.localRing K p) :=
  (lowerMap K S p).toAlgebra

scoped instance originalFieldTower : IsScalarTower
    (((S : Set (FinitePlace K)).integer K))
    (NumberFieldPlaceIntegralTensor.localRing K p) K := .of_algebraMap_eq fun _ => rfl

/-- The original lower place has an actual nonzero center on the original global S-integer ring. -/
def centerPrime : HeightOneSpectrum
    (((S : Set (FinitePlace K)).integer K)) :=
  DedekindValuationOverring.prime
    (((S : Set (FinitePlace K)).integer K))
    K (NumberFieldPlaceIntegralTensor.localRing K p) (localRing_ne_top K p)

scoped instance localization : IsLocalization
    (centerPrime K S p).asIdeal.primeCompl (NumberFieldPlaceIntegralTensor.localRing K p) :=
  DedekindValuationOverring.isLocalization
    (((S : Set (FinitePlace K)).integer K))
    K (NumberFieldPlaceIntegralTensor.localRing K p) (localRing_ne_top K p)

scoped instance completedAlgebra : Algebra
    (((S : Set (FinitePlace K)).integer K))
    (p.adicCompletionIntegers K) :=
  ((NumberFieldPlaceIntegralTensor.completionMap K p).comp (lowerMap K S p)).toAlgebra

scoped instance completedTower : IsScalarTower
    (((S : Set (FinitePlace K)).integer K))
    (NumberFieldPlaceIntegralTensor.localRing K p) (p.adicCompletionIntegers K) :=
  .of_algebraMap_eq fun _ => rfl

variable (L : Type u) [Field L] [NumberField L] [Algebra K L]

scoped instance upperFieldTower : IsScalarTower
    (((S : Set (FinitePlace K)).integer K))
    (NumberFieldPlaceIntegralTensor.localRing K p) L := .of_algebraMap_eq fun _ => rfl

/-- Localizing the actual upper S-integers gives the original lower-place integral closure. -/
def localTensorEquiv :
    (NumberFieldPlaceIntegralTensor.localRing K p) ⊗[
      ((S : Set (FinitePlace K)).integer K)]
      ((((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) ≃ₐ[(NumberFieldPlaceIntegralTensor.localRing K p)]
      NumberFieldPlaceIntegralTensor.closure K p L :=
  integralClosureLocalizationTensorEquiv
    (((S : Set (FinitePlace K)).integer K))
    (NumberFieldPlaceIntegralTensor.localRing K p) _ L (centerPrime K S p).asIdeal.primeCompl

@[simp]
theorem localTensorEquiv_tmul (a : (NumberFieldPlaceIntegralTensor.localRing K p))
    (b : (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) :
    (localTensorEquiv K S p L
      (a ⊗ₜ[((S : Set (FinitePlace K)).integer K)] b) : L) =
      algebraMap K L (a : K) * (b : L) :=
  integralClosureLocalizationTensorEquiv_tmul
    (((S : Set (FinitePlace K)).integer K))
    (NumberFieldPlaceIntegralTensor.localRing K p) _ L (centerPrime K S p).asIdeal.primeCompl a b

/-- The actual completed-integer tensor of the original global S-integer coefficients. -/
def completedTensorEquiv :
    p.adicCompletionIntegers K ⊗[
      ((S : Set (FinitePlace K)).integer K)]
      ((((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) ≃ₐ[p.adicCompletionIntegers K]
      (∀ q : AdelicFunctoriality.FinitePlacesAbove L p, q.1.adicCompletionIntegers L) :=
  (((Algebra.TensorProduct.cancelBaseChange
      (((S : Set (FinitePlace K)).integer K))
      (NumberFieldPlaceIntegralTensor.localRing K p) (p.adicCompletionIntegers K) (p.adicCompletionIntegers K)
      ((((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L))).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl
      (R := p.adicCompletionIntegers K) (A₁ := p.adicCompletionIntegers K))
      (localTensorEquiv K S p L))).trans
    (NumberFieldPlaceIntegralTensor.tensorEquiv K p L))

/-- The comparison retains the original completed embedding and every original upper coefficient. -/
@[simp]
theorem completedTensorEquiv_tmul (a : p.adicCompletionIntegers K)
    (b : (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    (completedTensorEquiv K S p L
      (a ⊗ₜ[((S : Set (FinitePlace K)).integer K)] b) q :
        q.1.adicCompletion L) =
      AdelicFunctoriality.FiniteExtension.completionMap p q.1 a *
        algebraMap L (q.1.adicCompletion L) (b : L) := by
  simp only [completedTensorEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, NumberFieldPlaceIntegralTensor.tensorEquiv_tmul]
  change AdelicFunctoriality.FiniteExtension.completionMap p q.1 a *
    algebraMap L (q.1.adicCompletion L)
      (localTensorEquiv K S p L
        (1 ⊗ₜ[((S : Set (FinitePlace K)).integer K)] b) : L) = _
  simp only [localTensorEquiv_tmul, OneMemClass.coe_one, map_one, one_mul]

/-- Every original upper place above this lower place lies outside the full exceptional preimage. -/
theorem upper_notMem (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    q.1 ∉ numberFieldExceptionalPreimage (L := L) S := by
  have : q.1.asIdeal.LiesOver p.asIdeal := q.2
  have h : q.1.under (NumberField.RingOfIntegers K) = p := by
    apply HeightOneSpectrum.ext
    exact (Ideal.over_def q.1.asIdeal p.asIdeal).symm
  simpa [h] using (Fact.out : p ∉ S)

/-- Include the actual upper global coefficients in each original completed upper integer ring. -/
def upperMap (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) →+*
      q.1.adicCompletionIntegers L :=
  (NumberFieldPlaceIntegralTensor.completionMap L q.1).comp
    (((((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)).toSubring.subtype.codRestrict _
      fun b => by
        rw [NumberFieldPlaceIntegralTensor.localRing, valuationSubringAtPrime_eq_valuationSubring]
        exact b.property q.1 (upper_notMem K S p L q))

scoped instance upperCompletedAlgebra (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    Algebra
      ((((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L))
      (q.1.adicCompletionIntegers L) :=
  (upperMap K S p L q).toAlgebra

@[simp]
theorem upperMap_coe
    (b : (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    (upperMap K S p L q b : q.1.adicCompletion L) =
      algebraMap L (q.1.adicCompletion L) (b : L) := rfl

/-- The right tensor coefficient is exactly the original upper integral coefficient map. -/
@[simp]
theorem completedTensorEquiv_one_tmul
    (b : (((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    completedTensorEquiv K S p L
      (1 ⊗ₜ[((S : Set (FinitePlace K)).integer K)] b) q =
        algebraMap
          ((((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L))
          (q.1.adicCompletionIntegers L) b := by
  apply Subtype.ext
  simp only [completedTensorEquiv_tmul, OneMemClass.coe_one, map_one, one_mul]
  rfl

end Langlands.Global.NumberFieldSIntegerLocalTensor
