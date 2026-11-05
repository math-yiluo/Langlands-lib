import Langlands.Global.FiniteConstantCurveChart
import Langlands.Global.CurvePlaceCompletionExtension
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.NumberTheory.FunctionField

/-! # Finite integral closure of actual function-field valuation rings -/

noncomputable section

universe u v w

open IsDedekindDomain IntermediateField AlgebraicCurve
open scoped Polynomial Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.FiniteConstantCurveChart

namespace Langlands.Global

/-- Module-finite integral closure remains module-finite after arbitrary localization. -/
theorem finite_integralClosure_of_arbitrary_localization
    {R : Type u} {A : Type v} {L : Type w}
    [CommRing R] [CommRing A] [CommRing L]
    [Algebra R A] [Algebra R L] [Algebra A L] [IsScalarTower R A L]
    (M : Submonoid R) [IsLocalization M A]
    [Module.Finite R (integralClosure R L)] :
    Module.Finite A (integralClosure A L) := by
  let f : integralClosure R L →+* integralClosure A L :=
    { toFun := fun x => ⟨x.val, x.property.tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let : Algebra (integralClosure R L) (integralClosure A L) := f.toAlgebra
  let : IsScalarTower R (integralClosure R L) (integralClosure A L) :=
    .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (integralClosure R L) (integralClosure A L) L :=
    .of_algebraMap_eq fun _ => rfl
  let : IsLocalization (Algebra.algebraMapSubmonoid L M) L :=
    IsLocalization.of_le_isUnit (by
      rintro _ ⟨r, hr, rfl⟩
      change IsUnit ((algebraMap R L) r)
      simpa only [← IsScalarTower.algebraMap_apply R A L] using
        (IsLocalization.map_units A (⟨r, hr⟩ : M)).map (algebraMap A L))
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure R L) M) (integralClosure A L) :=
    IsLocalization.integralClosure (S := L) (Rf := A) (Sf := L) M
  exact Module.Finite.of_isLocalization R (integralClosure R L) M

namespace CurvePlaceIntegralClosure

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra K L]
  (s : K) [FiniteDimensional k⟮s⟯ K]
  (p : AlgebraicCurve.Place k K)

/-- The original normalized chart inclusion into a valuation ring integral on that chart. -/
def chartIntegersMap (hs : s ∈ p.toValuationSubring) :
    CurveModel.chartRing k ({s} : Set K) →+* p.toValuationSubring :=
  (CurveModel.chartRing k ({s} : Set K)).val.toRingHom.codRestrict _
    (fun x => CurveModel.chartRing_le_valuationSubring p.toValuationSubring
      p.algebraMap_mem' (Set.singleton_subset_iff.mpr hs) x.property)

variable [FiniteDimensional K L]

/-- An actual valuation ring integral on a finite normalized chart has finite integral closure. -/
theorem finite_of_chart (hs : s ∈ p.toValuationSubring) :
    Module.Finite p.toValuationSubring (integralClosure p.toValuationSubring L) := by
  let R := CurveModel.chartRing k ({s} : Set K)
  let : Algebra R p.toValuationSubring := (chartIntegersMap k K s p hs).toAlgebra
  let : IsScalarTower R K L := inferInstance
  let : IsScalarTower R p.toValuationSubring K := .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R p.toValuationSubring L := .of_algebraMap_eq fun _ => rfl
  let P := CurveModel.primeOfValuationSubring k s p.toValuationSubring
    p.algebraMap_mem' hs p.ne_top'
  have hP : HeightOneSpectrum.valuationSubringAtPrime K P = p.toValuationSubring :=
    FiniteConstantCurveChart.valuationSubringAtPrime_eq k K s _ _ hs _
  let e : HeightOneSpectrum.valuationSubringAtPrime K P ≃ₐ[R] p.toValuationSubring :=
    { toRingEquiv := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hP)
      commutes' x := by apply Subtype.ext; rfl }
  let : IsLocalization P.asIdeal.primeCompl p.toValuationSubring :=
    IsLocalization.isLocalization_of_algEquiv P.asIdeal.primeCompl e
  let : Module.Finite ℤ k := inferInstance
  let : Algebra.FiniteType ℤ k := inferInstance
  let : Algebra.FiniteType ℤ R :=
    (inferInstance : Algebra.FiniteType ℤ k).trans
      (inferInstance : Algebra.FiniteType k R)
  let : Module.Finite R (integralClosure R L) :=
    Langlands.AlgebraicGeometry.NoetherianApproximation.finite_integralClosure_of_normal_integer_finiteType
      R K L
  exact finite_integralClosure_of_arbitrary_localization P.asIdeal.primeCompl

end CurvePlaceIntegralClosure

variable {k K : Type u} (L : Type u) [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra K L]

/-- The actual integral closure of the original valuation ring in the original upper field. -/
abbrev curvePlaceIntegralClosure (p : AlgebraicCurve.Place k K) :=
  integralClosure p.toValuationSubring L

namespace CurvePlaceIntegralClosure

variable {L} (p : AlgebraicCurve.Place k K) [FiniteDimensional K L]

/-- The original upper field is the fraction field of the actual integral closure. -/
scoped instance fractionRing : IsFractionRing (curvePlaceIntegralClosure L p) L :=
  integralClosure.isFractionRing_of_finite_extension K L

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- All actual function-field valuation rings have finite integral closure in any finite extension. -/
scoped instance moduleFinite :
    Module.Finite p.toValuationSubring (curvePlaceIntegralClosure L p) := by
  let s := algebraMap (RatFunc k) K (RatFunc.X : RatFunc k)
  let : FiniteDimensional k⟮s⟯ K := FunctionField.FiniteDimensional.adjoin_algebraMap_X
  rcases p.toValuationSubring.mem_or_inv_mem s with hs | hs
  · exact finite_of_chart k K L s p hs
  · let : FiniteDimensional k⟮s⁻¹⟯ K := by
      rw [FiniteConstantCurveChart.adjoin_inverse_eq k K s]
      infer_instance
    exact finite_of_chart k K L s⁻¹ p hs

/-- The actual integral closure is Dedekind even for inseparable original presentations. -/
scoped instance dedekind : IsDedekindDomain (curvePlaceIntegralClosure L p) := by
  let R := p.toValuationSubring
  let C := curvePlaceIntegralClosure L p
  let : IsNoetherianRing C := isNoetherianRing_iff.mpr
    (isNoetherian_of_tower R (inferInstance : IsNoetherian R C))
  let : Algebra.IsIntegral R C := IsIntegralClosure.isIntegral_algebra R L
  refine (isDedekindDomain_iff C L).mpr ⟨inferInstance, inferInstance,
    Ring.DimensionLEOne.of_isIntegral R C, ?_⟩
  intro x hx
  exact ⟨IsIntegralClosure.mk' C x (isIntegral_trans (R := R) _ hx),
    IsIntegralClosure.algebraMap_mk' _ _ _⟩

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] in
/-- The integral-closure module rank is the original field degree. -/
theorem finrank_eq :
    Module.finrank p.toValuationSubring (curvePlaceIntegralClosure L p) =
      Module.finrank K L :=
  (IsFractionRing.finrank_eq p.toValuationSubring K (curvePlaceIntegralClosure L p) L).symm

/-- The fundamental ramification-inertia identity on all primes of the actual integral closure. -/
theorem sum_ramification_inertia :
    letI := Fintype.ofFinite (p.heightOneSpectrum.asIdeal.primesOver (curvePlaceIntegralClosure L p))
    (∑ P : p.heightOneSpectrum.asIdeal.primesOver (curvePlaceIntegralClosure L p),
      P.1.ramificationIdx p.toValuationSubring *
        P.1.inertiaDeg p.toValuationSubring) = Module.finrank K L := by
  let := Fintype.ofFinite (p.heightOneSpectrum.asIdeal.primesOver (curvePlaceIntegralClosure L p))
  exact (Ideal.sum_ramification_inertia_eq_finrank p.heightOneSpectrum.asIdeal
    (curvePlaceIntegralClosure L p)).trans (finrank_eq (L := L) p)

end CurvePlaceIntegralClosure

end Langlands.Global
