import Langlands.Global.InfinityType
import Langlands.Global.HeckeCharacterTransport

/-! # The normalized weight-one infinity character -/

noncomputable section

universe u

namespace Langlands.Global.CMHalfWeight

open NumberField

/-- Absolute value, regarded as a positive-real-valued complex unit. -/
def absoluteValue : ℂˣ →ₜ* ℂˣ where
  toMonoidHom := Units.map
    (Complex.ofRealHom.toMonoidHom.comp (normHom : ℂ →*₀ ℝ).toMonoidHom)
  continuous_toFun := (Complex.continuous_ofReal.comp continuous_norm).units_map _

@[simp]
theorem absoluteValue_coe (z : ℂˣ) :
    (absoluteValue z : ℂ) = (‖(z : ℂ)‖ : ℂ) := rfl

@[simp]
theorem absoluteValue_star (z : ℂˣ) : absoluteValue (star z) = absoluteValue z := by
  apply Units.ext
  simp

theorem mul_star_eq_absoluteValue_sq (z : ℂˣ) :
    z * star z = absoluteValue z ^ 2 := by
  apply Units.ext
  change (z : ℂ) * (starRingEnd ℂ) (z : ℂ) = (‖(z : ℂ)‖ : ℂ) ^ 2
  simpa only [Complex.ofReal_pow] using Complex.mul_conj' (z : ℂ)

/-- A local weight-one algebraic character divided by the absolute value. -/
def normalizedComplexCharacter (p q : ℤ) : ℂˣ →ₜ* ℂˣ :=
  InfinityType.complexCharacter p q / absoluteValue

@[simp]
theorem normalizedComplexCharacter_apply (p q : ℤ) (z : ℂˣ) :
    normalizedComplexCharacter p q z =
      (z ^ p * star z ^ q) / absoluteValue z := rfl

theorem normalizedComplexCharacter_conjugate {p q : ℤ} (hpq : p + q = 1)
    (z : ℂˣ) :
    normalizedComplexCharacter p q (star z) =
      (normalizedComplexCharacter p q z)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  simp only [normalizedComplexCharacter_apply, star_star, absoluteValue_star, div_mul_div_comm]
  have h : (star z ^ p * z ^ q) * (z ^ p * star z ^ q) = absoluteValue z ^ 2 := by
    calc
      _ = (z * star z) ^ (p + q) := by
        simp only [mul_zpow, zpow_add]
        ac_rfl
      _ = absoluteValue z ^ 2 := by rw [hpq, zpow_one, mul_star_eq_absoluteValue_sq]
  rw [h, ← sq, div_self']

/-- On real nonzero arguments the normalized character is the sign. -/
theorem normalizedComplexCharacter_of_star_eq {p q : ℤ} (hpq : p + q = 1)
    (z : ℂˣ) (hz : star z = z) :
    normalizedComplexCharacter p q z = z / absoluteValue z := by
  simp only [normalizedComplexCharacter_apply, hz, ← zpow_add, hpq, zpow_one]

variable {K : Type u} [Field K] [NumberField K]

/-- The product of the ordinary absolute values of the complex coordinates. -/
def normCharacter : (InfiniteAdeles K)ˣ →ₜ* ℂˣ where
  toFun x := ∏ v : InfinitePlace K, absoluteValue (InfinityType.coordinate v x)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, Finset.prod_mul_distrib]
  continuous_toFun := continuous_finsetProd _ fun v _ ↦
    absoluteValue.continuous.comp (InfinityType.coordinate v).continuous

@[simp]
theorem normCharacter_coe (x : (InfiniteAdeles K)ˣ) :
    (normCharacter x : ℂ) = ∏ v : InfinitePlace K,
      (‖(InfinityType.coordinate v x : ℂ)‖ : ℂ) := by
  change (Units.coeHom ℂ) (∏ v : InfinitePlace K, _) = _
  rw [map_prod]
  rfl

/-- The normalized infinity character used in the weight-one existence theorem. -/
def normalizedCharacter [IsTotallyComplex K] (t : InfinityType K) :
    (InfiniteAdeles K)ˣ →ₜ* ℂˣ := InfinityType.toCharacter t / normCharacter

theorem normalizedCharacter_apply [IsTotallyComplex K] (t : InfinityType K)
    (x : (InfiniteAdeles K)ˣ) :
    normalizedCharacter t x = ∏ v : InfinitePlace K,
      normalizedComplexCharacter (t v.embedding)
        (t (ComplexEmbedding.conjugate v.embedding)) (InfinityType.coordinate v x) := by
  change InfinityType.toCharacter t x / normCharacter x = _
  rw [InfinityType.toCharacter_apply]
  exact (Finset.prod_div_distrib (s := Finset.univ) _ _).symm

/-- The twist equation, with the exact absolute-value convention of the target. -/
theorem normalizedCharacter_twist [IsTotallyComplex K] (t : InfinityType K)
    (x : (InfiniteAdeles K)ˣ) :
    (normalizedCharacter t x : ℂ) *
        ∏ v : InfinitePlace K, (‖(InfinityType.coordinate v x : ℂ)‖ : ℂ) =
      (InfinityType.toCharacter t x : ℂ) := by
  rw [← normCharacter_coe]
  exact congrArg Units.val (div_mul_cancel (InfinityType.toCharacter t x) (normCharacter x))

/-- Coordinatewise conjugation inverts the normalized pure weight-one character. -/
theorem normalizedCharacter_of_coordinates_star [IsTotallyComplex K]
    {t : InfinityType K} (ht : t.IsPureOfWeight 1)
    {x y : (InfiniteAdeles K)ˣ}
    (hxy : ∀ v, InfinityType.coordinate v y = star (InfinityType.coordinate v x)) :
    normalizedCharacter t y = (normalizedCharacter t x)⁻¹ := by
  rw [normalizedCharacter_apply, normalizedCharacter_apply, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun v _ ↦ by
    rw [hxy v, normalizedComplexCharacter_conjugate (ht v.embedding)]

/-- Arithmetic complex conjugation acts by coordinatewise complex conjugation. -/
theorem normalizedCharacter_complexConj [IsCMField K] {t : InfinityType K}
    (ht : t.IsPureOfWeight 1) (x : (InfiniteAdeles K)ˣ) :
    normalizedCharacter t (ideleProductEquiv K
      (AdelicFunctoriality.ideleEquiv (IsCMField.complexConj K).toRingEquiv
        (infiniteIdelesInclusion K x))).1 = (normalizedCharacter t x)⁻¹ := by
  apply normalizedCharacter_of_coordinates_star ht
  intro v
  apply Units.ext
  rw [Units.coe_star]
  exact AdelicFunctoriality.ideleComplexConj_infinite_coordinate
    (infiniteIdelesInclusion K x) v

/-- On real coordinates the normalized character is the product of their signs. -/
theorem normalizedCharacter_of_coordinates_real [IsTotallyComplex K]
    {t : InfinityType K} (ht : t.IsPureOfWeight 1) (x : (InfiniteAdeles K)ˣ)
    (hx : ∀ v, star (InfinityType.coordinate v x) = InfinityType.coordinate v x) :
    normalizedCharacter t x = ∏ v : InfinitePlace K,
      InfinityType.coordinate v x / absoluteValue (InfinityType.coordinate v x) := by
  rw [normalizedCharacter_apply]
  exact Finset.prod_congr rfl fun v _ ↦
    normalizedComplexCharacter_of_star_eq (ht v.embedding) _ (hx v)

end Langlands.Global.CMHalfWeight
