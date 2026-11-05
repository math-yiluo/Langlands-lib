import Langlands.Global.NumberFieldSIntegerIntegralClosure
import Langlands.Global.IntegralClosureLocalizationTensor
import Langlands.Global.AdelicFunctoriality.IntegralTensorEquiv

noncomputable section

universe u

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct
  Langlands.Global.AdelicFunctoriality.FiniteExtension
  Langlands.Global.AdelicFunctoriality.IntegralTensor

namespace Langlands.Global.NumberFieldPlaceIntegralTensor

variable (K : Type u) [Field K] [NumberField K] (p : HeightOneSpectrum (NumberField.RingOfIntegers K))

/-- The original lower valuation ring, inside the original lower number field. -/
abbrev localRing := valuationSubringAtPrime K p

/-- The original local ring embeds in its original completed valuation ring. -/
def completionMap : localRing K p →+* p.adicCompletionIntegers K :=
  ((algebraMap K (p.adicCompletion K)).comp (localRing K p).subtype).codRestrict _
    fun a => by
      rw [mem_adicCompletionIntegers]
      change Valued.v ((a : K) : p.adicCompletion K) ≤ 1
      rw [valuedAdicCompletion_eq_valuation']
      exact valuationSubringAtPrime_le_valuation p a.property

@[simp]
theorem completionMap_coe (a : localRing K p) :
    (completionMap K p a : p.adicCompletion K) =
      algebraMap K (p.adicCompletion K) (a : K) := rfl

scoped instance completedAlgebra : Algebra (localRing K p) (p.adicCompletionIntegers K) :=
  (completionMap K p).toAlgebra

scoped instance completedTower :
    IsScalarTower (NumberField.RingOfIntegers K) (localRing K p)
      (p.adicCompletionIntegers K) := .of_algebraMap_eq fun a => by
  apply Subtype.ext
  exact IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K
    (p.adicCompletion K) a

variable (L : Type u) [Field L] [NumberField L] [Algebra K L]

scoped instance (priority := 50) upperFieldAlgebra : Algebra (localRing K p) L :=
  ((algebraMap K L).comp (localRing K p).subtype).toAlgebra

scoped instance upperFieldTower : IsScalarTower (localRing K p) K L :=
  .of_algebraMap_eq fun _ => rfl

scoped instance integerFieldTower :
    IsScalarTower (NumberField.RingOfIntegers K) (localRing K p) L :=
  .of_algebraMap_eq fun a =>
    IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K L a

/-- The actual local integral closure in the original upper field. -/
abbrev closure := integralClosure (localRing K p) L

/-- The original upper valuation ring above p contains the actual local integral closure. -/
def closureMap (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    closure K p L →+* valuationSubringAtPrime L q.1 := by
  letI : q.1.asIdeal.LiesOver p.asIdeal := q.2
  letI : IsFractionRing (valuationSubringAtPrime L q.1) L := inferInstance
  let f : localRing K p →+* valuationSubringAtPrime L q.1 :=
    ((algebraMap K L).comp (localRing K p).subtype).codRestrict _ fun a => by
      rw [valuationSubringAtPrime_eq_valuationSubring]
      exact (numberFieldPlace_algebraMap_integral_iff p q.1 (a : K)).mpr
        (valuationSubringAtPrime_le_valuation p a.property)
  letI : Algebra (localRing K p) (valuationSubringAtPrime L q.1) := f.toAlgebra
  letI : IsScalarTower (localRing K p) (valuationSubringAtPrime L q.1) L :=
    .of_algebraMap_eq fun _ => rfl
  exact (closure K p L).toSubring.subtype.codRestrict _ fun b => by
    change (b : L) ∈ valuationSubringAtPrime L q.1
    obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff L).mp
      (inferInstance : IsIntegrallyClosed (valuationSubringAtPrime L q.1))
      (b.property.tower_top : IsIntegral (valuationSubringAtPrime L q.1) (b : L))
    exact ha ▸ a.property

/-- The actual closure coefficient map to each original upper completed integer ring. -/
def upperMap (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    closure K p L →+* q.1.adicCompletionIntegers L :=
  (completionMap L q.1).comp (closureMap K p L q)

@[simp]
theorem upperMap_coe (q : AdelicFunctoriality.FinitePlacesAbove L p)
    (b : closure K p L) :
    (upperMap K p L q b : q.1.adicCompletion L) =
      algebraMap L (q.1.adicCompletion L) (b : L) := rfl

scoped instance upperAlgebra (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    Algebra (closure K p L) (q.1.adicCompletionIntegers L) :=
  (upperMap K p L q).toAlgebra

scoped instance upperBaseAlgebra (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    Algebra (localRing K p) (q.1.adicCompletionIntegers L) :=
  ((upperMap K p L q).comp (algebraMap (localRing K p) (closure K p L))).toAlgebra

scoped instance closureTower (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    IsScalarTower (localRing K p) (closure K p L) (q.1.adicCompletionIntegers L) :=
  .of_algebraMap_eq fun _ => rfl

scoped instance upperCompletedTower (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    IsScalarTower (localRing K p) (p.adicCompletionIntegers K)
      (q.1.adicCompletionIntegers L) := .of_algebraMap_eq fun a => by
  apply Subtype.ext
  change algebraMap L (q.1.adicCompletion L) (algebraMap K L (a : K)) =
    AdelicFunctoriality.FiniteExtension.completionMap p q.1
      (algebraMap K (p.adicCompletion K) (a : K))
  rw [AdelicFunctoriality.FiniteExtension.completionMap_coe]

/-- Multiply the two original completed local coefficient maps in every original upper factor. -/
def tensorMap :
    p.adicCompletionIntegers K ⊗[localRing K p] closure K p L →ₐ[
      p.adicCompletionIntegers K]
      (∀ q : AdelicFunctoriality.FinitePlacesAbove L p, q.1.adicCompletionIntegers L) :=
  AlgHom.pi fun q => Algebra.TensorProduct.lift
    (Algebra.ofId (p.adicCompletionIntegers K) (q.1.adicCompletionIntegers L))
    (Algebra.algHom (localRing K p) (closure K p L) (q.1.adicCompletionIntegers L))
    (fun _ _ => .all _ _)

@[simp]
theorem tensorMap_tmul (a : p.adicCompletionIntegers K) (b : closure K p L)
    (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    (tensorMap K p L (a ⊗ₜ[localRing K p] b) q : q.1.adicCompletion L) =
      AdelicFunctoriality.FiniteExtension.completionMap p q.1 a *
        algebraMap L (q.1.adicCompletion L) (b : L) := rfl

/-- Localization of the original global integer coefficients gives the actual local closure. -/
def localizationTensorEquiv :
    localRing K p ⊗[NumberField.RingOfIntegers K] (NumberField.RingOfIntegers L) ≃ₐ[
      localRing K p] closure K p L :=
  integralClosureLocalizationTensorEquiv (NumberField.RingOfIntegers K)
    (localRing K p) (NumberField.RingOfIntegers L) L p.asIdeal.primeCompl

/-- The original completed global integer tensor is unchanged by localizing at p first. -/
def completedLocalizationEquiv :
    p.adicCompletionIntegers K ⊗[NumberField.RingOfIntegers K]
      (NumberField.RingOfIntegers L) ≃ₐ[p.adicCompletionIntegers K]
      (p.adicCompletionIntegers K ⊗[localRing K p] closure K p L) :=
  ((Algebra.TensorProduct.cancelBaseChange (NumberField.RingOfIntegers K)
    (localRing K p) (p.adicCompletionIntegers K) (p.adicCompletionIntegers K)
    (NumberField.RingOfIntegers L)).symm).trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl (R := p.adicCompletionIntegers K) (A₁ := p.adicCompletionIntegers K))
        (localizationTensorEquiv K p L))

/-- The local-closure map agrees with the published original global-integer tensor map. -/
theorem tensorMap_completedLocalizationEquiv
    (z : p.adicCompletionIntegers K ⊗[NumberField.RingOfIntegers K]
      (NumberField.RingOfIntegers L)) :
    tensorMap K p L (completedLocalizationEquiv K p L z) =
      AdelicFunctoriality.IntegralTensor.tensorMap (L := L) p z := by
  induction z with
  | tmul a b =>
    apply funext
    intro q
    apply Subtype.ext
    simp only [completedLocalizationEquiv, AlgEquiv.trans_apply,
      Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul, AdelicFunctoriality.IntegralTensor.tensorMap_tmul]
    change AdelicFunctoriality.FiniteExtension.completionMap p q.1 a *
        algebraMap L (q.1.adicCompletion L)
          (localizationTensorEquiv K p L
            (1 ⊗ₜ[NumberField.RingOfIntegers K] b) : L) = _
    rw [localizationTensorEquiv, integralClosureLocalizationTensorEquiv_tmul]
    simp only [map_one, one_mul]
    exact congrArg (fun x => AdelicFunctoriality.FiniteExtension.completionMap p q.1 a * x)
      (IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers L) L
        (q.1.adicCompletion L) b).symm
  | add z w hz hw =>
    simp only [map_add, hz, hw]

theorem tensorMap_bijective : Function.Bijective (tensorMap K p L) := by
  constructor
  · intro x y h
    obtain ⟨z, rfl⟩ := (completedLocalizationEquiv K p L).surjective x
    obtain ⟨w, rfl⟩ := (completedLocalizationEquiv K p L).surjective y
    rw [tensorMap_completedLocalizationEquiv, tensorMap_completedLocalizationEquiv] at h
    exact congrArg (completedLocalizationEquiv K p L)
      ((AdelicFunctoriality.IntegralTensor.tensorEquiv (L := L) p).injective h)
  · intro x
    obtain ⟨z, hz⟩ := (AdelicFunctoriality.IntegralTensor.tensorEquiv (L := L) p).surjective x
    exact ⟨completedLocalizationEquiv K p L z,
      (tensorMap_completedLocalizationEquiv K p L z).trans hz⟩

/-- The completed original local integral closure decomposes over all original upper places. -/
def tensorEquiv :
    p.adicCompletionIntegers K ⊗[localRing K p] closure K p L ≃ₐ[
      p.adicCompletionIntegers K]
      (∀ q : AdelicFunctoriality.FinitePlacesAbove L p, q.1.adicCompletionIntegers L) :=
  AlgEquiv.ofBijective (tensorMap K p L) (tensorMap_bijective K p L)

@[simp]
theorem tensorEquiv_tmul (a : p.adicCompletionIntegers K) (b : closure K p L)
    (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    (tensorEquiv K p L (a ⊗ₜ[localRing K p] b) q : q.1.adicCompletion L) =
      AdelicFunctoriality.FiniteExtension.completionMap p q.1 a *
        algebraMap L (q.1.adicCompletion L) (b : L) := rfl

@[simp]
theorem tensorEquiv_one_tmul (b : closure K p L)
    (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    tensorEquiv K p L (1 ⊗ₜ[localRing K p] b) q =
      algebraMap (closure K p L) (q.1.adicCompletionIntegers L) b := by
  apply Subtype.ext
  simp only [tensorEquiv_tmul, OneMemClass.coe_one, map_one, one_mul]
  rfl

end Langlands.Global.NumberFieldPlaceIntegralTensor
