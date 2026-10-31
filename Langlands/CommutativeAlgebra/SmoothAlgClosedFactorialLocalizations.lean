import Langlands.CommutativeAlgebra.FlatLocalFactorialDescent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Factorial prime localizations of smooth algebras over algebraically closed fields

Assuming the completion identification and the factoriality of power series rings, every
prime localization of a smooth algebra over an algebraically closed field is factorial.
-/

universe u

namespace Langlands.CommutativeAlgebra

open IsLocalRing

/-- A Noetherian local ring whose `𝔪`-adic completion is factorial is factorial. -/
theorem uniqueFactorizationMonoid_of_adicCompletion (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [UniqueFactorizationMonoid (AdicCompletion (maximalIdeal R) R)] :
    UniqueFactorizationMonoid R :=
  uniqueFactorizationMonoid_of_flat_of_isLocalHom (S := AdicCompletion (maximalIdeal R) R)

/-- At a maximal ideal of a finite type algebra over an algebraically closed field `K`, the
residue field of the localization is `K`. -/
theorem surjective_algebraMap_residueField_of_isAlgClosed (K A : Type*) [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    Function.Surjective (algebraMap K (ResidueField (Localization.AtPrime m))) := by
  have : Algebra.FiniteType K m.ResidueField := Algebra.FiniteType.trans (S := A) inferInstance
    inferInstance
  have : Module.Finite K m.ResidueField := finite_of_finite_type_of_isJacobsonRing K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := m.ResidueField)).2

/-- **Factoriality at closed points.** The localization of a smooth algebra over an
algebraically closed field at a maximal ideal is factorial, given the completion
identification `hcompl` and the factoriality `hps` of power series rings. -/
theorem uniqueFactorizationMonoid_localization_maximal_of_smooth {K : Type u} [Field K]
    [IsAlgClosed K] {A : Type u} [CommRing A] [Algebra K A] [Algebra.Smooth K A]
    (hcompl : ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra K R]
      [Algebra.FormallySmooth K R], Function.Surjective (algebraMap K (ResidueField R)) →
        ∃ n : ℕ, Nonempty (AdicCompletion (maximalIdeal R) R ≃+* MvPowerSeries (Fin n) K))
    (hps : ∀ n : ℕ, UniqueFactorizationMonoid (MvPowerSeries (Fin n) K))
    (m : Ideal A) [m.IsMaximal] : UniqueFactorizationMonoid (Localization.AtPrime m) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  obtain ⟨n, ⟨e⟩⟩ := hcompl (Localization.AtPrime m)
    (surjective_algebraMap_residueField_of_isAlgClosed K A m)
  have : UniqueFactorizationMonoid
      (AdicCompletion (maximalIdeal (Localization.AtPrime m)) (Localization.AtPrime m)) :=
    e.symm.toMulEquiv.uniqueFactorizationMonoid (hps n)
  exact uniqueFactorizationMonoid_of_adicCompletion _

/-- **Factoriality at all points.** Every prime localization of a smooth algebra over an
algebraically closed field is factorial, given the completion identification `hcompl` and
the factoriality `hps` of power series rings. -/
theorem uniqueFactorizationMonoid_localization_of_smooth {K : Type u} [Field K]
    [IsAlgClosed K] {A : Type u} [CommRing A] [Algebra K A] [Algebra.Smooth K A]
    (hcompl : ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra K R]
      [Algebra.FormallySmooth K R], Function.Surjective (algebraMap K (ResidueField R)) →
        ∃ n : ℕ, Nonempty (AdicCompletion (maximalIdeal R) R ≃+* MvPowerSeries (Fin n) K))
    (hps : ∀ n : ℕ, UniqueFactorizationMonoid (MvPowerSeries (Fin n) K))
    (P : Ideal A) [P.IsPrime] : UniqueFactorizationMonoid (Localization.AtPrime P) := by
  obtain ⟨m, hm, hPm⟩ := P.exists_le_maximal (Ideal.IsPrime.ne_top ‹_›)
  have := uniqueFactorizationMonoid_localization_maximal_of_smooth hcompl hps m
  let P' : Ideal (Localization.AtPrime m) := P.map (algebraMap A (Localization.AtPrime m))
  have hdisj : Disjoint (m.primeCompl : Set A) P := by
    rw [Set.disjoint_left]
    intro a ha haP
    exact ha (hPm haP)
  have : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl _ P ‹_› hdisj
  have hcomap : P'.under A = P :=
    IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ ‹_› hdisj
  have h1 : IsLocalization (P'.under A).primeCompl (Localization.AtPrime P') :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization m.primeCompl _ P'
  have hcompl' : (P'.under A).primeCompl = P.primeCompl := by
    ext x
    simp only [Ideal.mem_primeCompl_iff, hcomap]
  rw [hcompl'] at h1
  let e := IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
    (Localization.AtPrime P')
  exact e.symm.toMulEquiv.uniqueFactorizationMonoid inferInstance

end Langlands.CommutativeAlgebra
