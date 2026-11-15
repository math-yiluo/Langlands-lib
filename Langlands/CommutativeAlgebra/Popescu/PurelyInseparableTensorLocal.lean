import Langlands.CommutativeAlgebra.RegularRingMaps
import Langlands.GroupScheme.FiniteFieldTorsorPoint.LangAlgebra
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Purely inseparable base change of a local ring -/

universe u v

namespace Langlands.CommutativeAlgebra.Popescu.Faltings

open scoped TensorProduct
open Algebra.TensorProduct

section Radicial

variable (k : Type*) [Field k] (k' : Type*) [Field k'] [Algebra k k']
  [IsPurelyInseparable k k'] (A : Type*) [CommRing A] [Algebra k A]

/-- Every element of `A ⊗[k] k'` has a `p`-power iterate coming from `A`, when `k'/k` is purely
inseparable of exponential characteristic `p`. -/
theorem exists_pow_eq_algebraMap (p : ℕ) [ExpChar k p] [Nontrivial A] (z : A ⊗[k] k') :
    ∃ (n : ℕ) (a : A), z ^ p ^ n = algebraMap A (A ⊗[k] k') a := by
  have hinj : Function.Injective (includeLeft : A →ₐ[k] A ⊗[k] k') :=
    Algebra.TensorProduct.includeLeft_injective (algebraMap k k').injective
  have : Nontrivial (A ⊗[k] k') := hinj.nontrivial
  have : ExpChar (A ⊗[k] k') p :=
    expChar_of_injective_algebraMap (algebraMap k (A ⊗[k] k')).injective p
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem k p x
    refine ⟨n, algebraMap k A c * a ^ p ^ n, ?_⟩
    rw [tmul_pow, ← hc, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, Algebra.algebraMap_eq_smul_one (A := k') c, ← TensorProduct.smul_tmul,
      Algebra.smul_def]
  | add z w hz hw =>
    obtain ⟨n, a, ha⟩ := hz
    obtain ⟨m, b, hb⟩ := hw
    refine ⟨n + m, a ^ p ^ m + b ^ p ^ n, ?_⟩
    rw [add_pow_expChar_pow, map_add, map_pow, map_pow, ← ha, ← hb, ← pow_mul, ← pow_mul,
      ← pow_add, ← pow_add, add_comm m n]

/-- A purely inseparable base change of a local algebra over a field is local. -/
theorem isLocalRing_tensor [IsLocalRing A] : IsLocalRing (A ⊗[k] k') := by
  obtain ⟨p, _⟩ := ExpChar.exists k
  have hinj : Function.Injective (includeLeft : A →ₐ[k] A ⊗[k] k') :=
    Algebra.TensorProduct.includeLeft_injective (algebraMap k k').injective
  have : Nontrivial (A ⊗[k] k') := hinj.nontrivial
  have : ExpChar (A ⊗[k] k') p :=
    expChar_of_injective_algebraMap (algebraMap k (A ⊗[k] k')).injective p
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨n, a, ha⟩ := exists_pow_eq_algebraMap k k' A p z
  have hn : p ^ n ≠ 0 := pow_ne_zero _ (expChar_pos k p).ne'
  have h1 : (1 - z) ^ p ^ n = algebraMap A (A ⊗[k] k') (1 - a) := by
    rw [sub_pow_expChar_pow, one_pow, ha, map_sub, map_one]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
  · left
    rw [← isUnit_pow_iff hn, ha]
    exact h.map _
  · right
    rw [← isUnit_pow_iff hn, h1]
    exact h.map _

/-- A purely inseparable base change `A → A ⊗[k] k'` is integral. -/
theorem isIntegral_tensor [Nontrivial A] : Algebra.IsIntegral A (A ⊗[k] k') := by
  obtain ⟨p, _⟩ := ExpChar.exists k
  refine ⟨fun z => ?_⟩
  obtain ⟨n, a, ha⟩ := exists_pow_eq_algebraMap k k' A p z
  refine ⟨Polynomial.X ^ p ^ n - Polynomial.C a,
    Polynomial.monic_X_pow_sub_C a (pow_ne_zero _ (expChar_pos k p).ne'), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, ha, sub_self]

/-- A purely inseparable base change does not increase the Krull dimension. -/
theorem ringKrullDim_tensor_le [Nontrivial A] :
    ringKrullDim (A ⊗[k] k') ≤ ringKrullDim A := by
  have := isIntegral_tensor k k' A
  exact Langlands.GroupScheme.FiniteFieldTorsorPoint.ringKrullDim_le_of_isIntegral

end Radicial

/-- A localization of a regular ring is regular. -/
theorem isRegularRing_of_isLocalization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] [IsRegularRing R] : IsRegularRing S := by
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing M S inferInstance
  refine isRegularRing_iff.mpr fun P _ => ?_
  have : IsLocalization.AtPrime (Localization.AtPrime P) (P.comap (algebraMap R S)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime P) P
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (P.comap (algebraMap R S)).primeCompl
      (Localization.AtPrime (P.comap (algebraMap R S))) (Localization.AtPrime P)).toRingEquiv

section Geometric

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']
  {Λ : Type v} [CommRing Λ] [Algebra k Λ] (q : Ideal Λ) [q.IsPrime]

/-- `k' ⊗[k] Λ_q` is a localization of `k' ⊗[k] Λ`. -/
theorem isLocalization_tensor_atPrime :
    letI : Algebra (k' ⊗[k] Λ) (k' ⊗[k] Localization.AtPrime q) :=
      (Algebra.TensorProduct.map (AlgHom.id k k')
        (IsScalarTower.toAlgHom k Λ (Localization.AtPrime q))).toAlgebra
    IsLocalization (q.primeCompl.map (includeRight (R := k) (A := k')))
      (k' ⊗[k] Localization.AtPrime q) := by
  let : Algebra (k' ⊗[k] Λ) (k' ⊗[k] Localization.AtPrime q) :=
    (Algebra.TensorProduct.map (AlgHom.id k k')
      (IsScalarTower.toAlgHom k Λ (Localization.AtPrime q))).toAlgebra
  have : IsScalarTower k' (k' ⊗[k] Λ) (k' ⊗[k] Localization.AtPrime q) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  exact IsLocalization.tensorProduct_tensorProduct_right k k' q.primeCompl
    (Localization.AtPrime q) (by ext; simp [RingHom.algebraMap_toAlgebra])

variable [IsPurelyInseparable k k']

/-- (L3)(i): `Λ_q ⊗[k] k'` is a local ring. -/
theorem isLocalRing_tensor_atPrime : IsLocalRing (Localization.AtPrime q ⊗[k] k') :=
  isLocalRing_tensor k k' _

/-- (L3)(ii): for `Λ` geometrically regular over `k`, `Λ_q ⊗[k] k'` is a regular local ring. -/
theorem isRegularLocalRing_tensor_atPrime [FiniteDimensional k k']
    (hΛ : GeometricallyRegular k Λ) :
    IsRegularLocalRing (Localization.AtPrime q ⊗[k] k') := by
  have : IsRegularRing (k' ⊗[k] Λ) := hΛ.2 k'
  let : Algebra (k' ⊗[k] Λ) (k' ⊗[k] Localization.AtPrime q) :=
    (Algebra.TensorProduct.map (AlgHom.id k k')
      (IsScalarTower.toAlgHom k Λ (Localization.AtPrime q))).toAlgebra
  have := isLocalization_tensor_atPrime k k' q
  have : IsRegularRing (k' ⊗[k] Localization.AtPrime q) :=
    isRegularRing_of_isLocalization (q.primeCompl.map (includeRight (R := k) (A := k')))
  have := isLocalRing_tensor_atPrime k k' q
  have : IsLocalRing (k' ⊗[k] Localization.AtPrime q) :=
    (Algebra.TensorProduct.comm k (Localization.AtPrime q) k').toRingEquiv.isLocalRing
  have : IsRegularLocalRing (k' ⊗[k] Localization.AtPrime q) :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  exact IsRegularLocalRing.of_ringEquiv
    (Algebra.TensorProduct.comm k k' (Localization.AtPrime q)).toRingEquiv

/-- (L3)(iii): `dim (Λ_q ⊗[k] k') ≤ dim Λ_q`. -/
theorem ringKrullDim_tensor_atPrime_le :
    ringKrullDim (Localization.AtPrime q ⊗[k] k') ≤ ringKrullDim (Localization.AtPrime q) :=
  ringKrullDim_tensor_le k k' _

end Geometric

end Langlands.CommutativeAlgebra.Popescu.Faltings
