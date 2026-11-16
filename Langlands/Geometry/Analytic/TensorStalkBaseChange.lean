import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Localization of the right factor and pointwise base change -/

noncomputable section

universe u v w

namespace Langlands.Analytic.TensorStalkBaseChange

open scoped TensorProduct

variable {R : Type u} {S : Type v} {T : Type w}
  [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- Localizing the right tensor factor is canonically the localization of the
ordinary tensor product at the corresponding right-factor denominators. -/
def tensorLocalizationEquiv (q : Ideal S) [q.IsPrime] :
    T ⊗[R] Localization.AtPrime q ≃ₐ[T]
      Localization (q.primeCompl.map
        (Algebra.TensorProduct.includeRight (R := R) (A := T))) :=
  IsLocalization.tensorProductEquivOfMapIncludeRight R T q.primeCompl
    (Localization.AtPrime q) _

/-- Flatness of the localized right factor survives arbitrary coefficient
base change and subsequent localization at a prime of the tensor product. -/
theorem flat_atPrime (P : Ideal (T ⊗[R] S)) [P.IsPrime]
    (hflat : Module.Flat R (Localization.AtPrime
      (P.comap (Algebra.TensorProduct.includeRight (R := R) (A := T)).toRingHom))) :
    Module.Flat T (Localization.AtPrime P) := by
  let q : Ideal S := P.comap
    (Algebra.TensorProduct.includeRight (R := R) (A := T)).toRingHom
  have : q.IsPrime := Ideal.IsPrime.comap _
  let N : Submonoid (T ⊗[R] S) := q.primeCompl.map
    (Algebra.TensorProduct.includeRight (R := R) (A := T))
  have hNP : N ≤ P.primeCompl := by
    rintro _ ⟨s, hs, rfl⟩
    exact hs
  let D := Localization N
  let : Algebra D (Localization.AtPrime P) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe D (Localization.AtPrime P)
      N P.primeCompl hNP
  have : IsScalarTower (T ⊗[R] S) D (Localization.AtPrime P) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le D (Localization.AtPrime P)
      N P.primeCompl hNP
  have : IsScalarTower T D (Localization.AtPrime P) :=
    IsScalarTower.to₁₃₄ T (T ⊗[R] S) D (Localization.AtPrime P)
  have : IsLocalization (P.primeCompl.map (algebraMap (T ⊗[R] S) D))
      (Localization.AtPrime P) :=
    IsLocalization.isLocalization_of_submonoid_le D (Localization.AtPrime P)
      N P.primeCompl hNP
  have : Module.Flat R (Localization.AtPrime q) := hflat
  have : Module.Flat T (T ⊗[R] Localization.AtPrime q) := inferInstance
  have : Module.Flat T D :=
    Module.Flat.of_linearEquiv (tensorLocalizationEquiv (R := R) (T := T) q).symm.toLinearEquiv
  have : Module.Flat D (Localization.AtPrime P) :=
    IsLocalization.flat _ (P.primeCompl.map (algebraMap (T ⊗[R] S) D))
  exact Module.Flat.trans T D (Localization.AtPrime P)

/-- Formal unramifiedness of the localized right factor survives arbitrary
coefficient base change and localization at a prime of the tensor product. -/
theorem formallyUnramified_atPrime (P : Ideal (T ⊗[R] S)) [P.IsPrime]
    (hunr : Algebra.FormallyUnramified R (Localization.AtPrime
      (P.comap (Algebra.TensorProduct.includeRight (R := R) (A := T)).toRingHom))) :
    Algebra.FormallyUnramified T (Localization.AtPrime P) := by
  let q : Ideal S := P.comap
    (Algebra.TensorProduct.includeRight (R := R) (A := T)).toRingHom
  have : q.IsPrime := Ideal.IsPrime.comap _
  let N : Submonoid (T ⊗[R] S) := q.primeCompl.map
    (Algebra.TensorProduct.includeRight (R := R) (A := T))
  have hNP : N ≤ P.primeCompl := by
    rintro _ ⟨s, hs, rfl⟩
    exact hs
  let D := Localization N
  let : Algebra D (Localization.AtPrime P) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe D (Localization.AtPrime P)
      N P.primeCompl hNP
  have : IsScalarTower (T ⊗[R] S) D (Localization.AtPrime P) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le D (Localization.AtPrime P)
      N P.primeCompl hNP
  have : IsScalarTower T D (Localization.AtPrime P) :=
    IsScalarTower.to₁₃₄ T (T ⊗[R] S) D (Localization.AtPrime P)
  have : IsLocalization (P.primeCompl.map (algebraMap (T ⊗[R] S) D))
      (Localization.AtPrime P) :=
    IsLocalization.isLocalization_of_submonoid_le D (Localization.AtPrime P)
      N P.primeCompl hNP
  have : Algebra.FormallyUnramified R (Localization.AtPrime q) := hunr
  have : Algebra.FormallyUnramified T (T ⊗[R] Localization.AtPrime q) := inferInstance
  have : Algebra.FormallyUnramified T D :=
    Algebra.FormallyUnramified.of_equiv (tensorLocalizationEquiv (R := R) (T := T) q)
  have : Algebra.FormallyUnramified D (Localization.AtPrime P) :=
    Algebra.FormallyUnramified.of_isLocalization
      (P.primeCompl.map (algebraMap (T ⊗[R] S) D))
  exact Algebra.FormallyUnramified.comp T D (Localization.AtPrime P)

end Langlands.Analytic.TensorStalkBaseChange
