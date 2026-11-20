import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.NormalizationBaseChange
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Localizing an integral closure by tensoring the base with a localization -/

open TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

variable (R D H : Type*) [CommRing R] [CommRing D] [CommRing H]
    [Algebra R D] [Algebra R H] [Algebra D H] [IsScalarTower R D H]
    (M : Submonoid R)

local notation "Rₘ" => Localization M
local notation "Dₘ" => Rₘ ⊗[R] D
local notation "Hₘ" => Rₘ ⊗[R] H
local notation "C" => integralClosure D H

local instance : Algebra Dₘ Hₘ := tensorBaseChangeAlgebra R Rₘ D (B := H)
local notation "Cₘ" => integralClosure Dₘ Hₘ

local instance : Algebra H Hₘ := Algebra.TensorProduct.rightAlgebra
local instance : Algebra D Dₘ := Algebra.TensorProduct.rightAlgebra
local instance : Algebra D Hₘ := Algebra.compHom Hₘ (algebraMap D H)
local instance : IsScalarTower D H Hₘ := IsScalarTower.of_algebraMap_eq fun _ => rfl
local instance : IsScalarTower D Dₘ Hₘ := IsScalarTower.of_algebraMap_eq fun _ => rfl
local instance : IsScalarTower R D Dₘ := Algebra.TensorProduct.right_isScalarTower
local instance : IsScalarTower R H Hₘ := Algebra.TensorProduct.right_isScalarTower

/-- The normalization map induced by tensoring both rings with a localization
of the underlying scalar ring. -/
def integralClosureTensorLocalizationMap : C →ₐ[D] Cₘ := integralClosureLocalizedMap

local instance : Algebra C Cₘ := (integralClosureTensorLocalizationMap R D H M).toRingHom.toAlgebra
local instance : IsScalarTower C Cₘ Hₘ := by
  exact IsScalarTower.of_algebraMap_eq (R := C) (S := Cₘ) (A := Hₘ) fun _ => rfl
local instance : IsScalarTower D C Cₘ := IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Integral closure after localizing the base by tensor product is a
localization of the original integral closure at the corresponding scalars. -/
theorem isLocalization_integralClosureTensorLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid C M) Cₘ := by
  let N := Algebra.algebraMapSubmonoid D M
  have : IsLocalization N Dₘ := IsLocalization.tensorRight Rₘ M
  have : IsLocalization (Algebra.algebraMapSubmonoid H M) Hₘ := IsLocalization.tensorRight Rₘ M
  have : IsLocalization (Algebra.algebraMapSubmonoid H N) Hₘ := by
    simpa only [N, Algebra.algebraMapSubmonoid_map_map] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid H M) Hₘ)
  simpa only [N, Algebra.algebraMapSubmonoid_map_map] using
    (IsLocalization.integralClosure (R := D) (S := H) (Rf := Dₘ) (Sf := Hₘ) N)

/-- A local ring in the normalization after localizing the base is the
local ring of the original normalization at the contracted prime. -/
def integralClosureTensorLocalizationAtPrimeEquiv (q : Ideal Cₘ) [q.IsPrime] :
    letI : Algebra C (Localization.AtPrime q) :=
      Algebra.compHom _ (algebraMap C Cₘ)
    Localization.AtPrime (q.under C) ≃ₐ[C] Localization.AtPrime q := by
  let T := Localization.AtPrime q
  let alg := Algebra.compHom T (algebraMap C Cₘ)
  let : Algebra C T := alg
  let : SMul C T := alg.toSMul
  let : SMul Cₘ T := (inferInstance : Algebra Cₘ T).toSMul
  have : IsScalarTower C Cₘ T := by
    exact IsScalarTower.of_algebraMap_eq (R := C) (S := Cₘ) (A := T) fun _ => rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid C M) Cₘ :=
    isLocalization_integralClosureTensorLocalization R D H M
  have : IsLocalization.AtPrime T (q.under C) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid C M) T q
  exact IsLocalization.algEquiv (q.under C).primeCompl _ _

/-- Over a prime `p` of the original scalar ring, primes of the localized
integral closure are maximal when the closure was integral over the scalars. -/
theorem isMaximal_integralClosureTensorLocalization_of_under [Algebra.IsIntegral R C]
    (p : Ideal R) [p.IsPrime] (hM : M = p.primeCompl) (q : Ideal Cₘ) [q.IsPrime]
    (hqp : (q.under C).under R = p) : q.IsMaximal := by
  let M' := Algebra.algebraMapSubmonoid C M
  have : IsLocalization M' Cₘ := isLocalization_integralClosureTensorLocalization R D H M
  obtain ⟨J, hJ, hle⟩ := q.exists_le_maximal (Ideal.IsPrime.ne_top inferInstance)
  by_cases he : q = J
  · exact he.symm ▸ hJ
  have hlt : q.under C < J.under C :=
    (IsLocalization.orderEmbedding M' Cₘ).lt_iff_lt.mpr (lt_of_le_of_ne hle he)
  have hcontra := Ideal.IsIntegral.under_lt_under (R := R) hlt
  have hJp : (J.under C).under R ≤ p := by
    intro r hr
    by_contra hnr
    have hrM : r ∈ M := hM.symm ▸ hnr
    have hdisj := (IsLocalization.disjoint_under_iff M' Cₘ J).mpr hJ.ne_top
    exact Set.disjoint_left.mp hdisj ⟨r, hrM, rfl⟩ hr
  exact ((not_lt_of_ge hJp) (hqp ▸ hcontra)).elim

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
