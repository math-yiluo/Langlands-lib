import Langlands.Representation.Archimedean.RealInducedSwapLimit

/-!
# Balanced scalar normalizations of the regular crossing families

An analytic family can use either the raw regularization or its simple
quotient. Opposite families specialize an inverse when their removed and
divided orders balance, including a reciprocal zero and pole.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealInducedSwapBalanced

open Langlands.LocalFactor.Archimedean
open RealCharacterInducedSwap RealInducedSwapGeneric RealInducedSwapInverse
open RealInducedSwapRegularizedFamily RealInducedSwapRegularization
open RealInducedSwapGerm RealBlockMultiplierAnalytic RealFiniteLayerRegularization
open scoped Topology

/-- Choices of removed denominators and whether to divide by one parameter. -/
structure Normalization where
  choices : Choices
  divide : Bool

/-- The order of the optional simple division. -/
def divisionOrder (a : Normalization) : ℕ := if a.divide then 1 else 0

/-- The scalar formulas are valid, and any division has a cancelled center. -/
def IsValid (d e : ComplexCharacterData) (a : Normalization) : Prop :=
  Valid d e a.choices ∧ (a.divide = true → Cancels d e a.choices)

/-- The opposite families remove as many denominators as they divide out. -/
def Balanced (a b : Normalization) : Prop :=
  totalOrder a.choices + totalOrder b.choices = divisionOrder a + divisionOrder b

/-- The scalar relating this family to the generic shifted map. -/
def scalar (a : Normalization) (z : ℂ) : ℂ :=
  z ^ totalOrder a.choices / z ^ divisionOrder a

theorem scalar_ne_zero (a : Normalization) {z : ℂ} (hz : z ≠ 0) :
    scalar a z ≠ 0 :=
  div_ne_zero (pow_ne_zero _ hz) (pow_ne_zero _ hz)

theorem scalar_mul (a : Normalization) (x y : ℂ) :
    scalar a (x * y) = scalar a x * scalar a y := by
  simp only [scalar, mul_pow, div_mul_div_comm]

theorem scalar_product {a b : Normalization} (hab : Balanced a b)
    {z : ℂ} (hz : z ≠ 0) : scalar a z * scalar b z = 1 := by
  rw [scalar, scalar, div_mul_div_comm, ← pow_add, ← pow_add, hab]
  exact div_self (pow_ne_zero _ hz)

theorem scalar_product_neg {a b : Normalization} (hab : Balanced a b)
    {z : ℂ} (hz : z ≠ 0) :
    scalar b (-z) * scalar a z = scalar b (-1) := by
  rw [show -z = (-1 : ℂ) * z by ring, scalar_mul]
  rw [mul_assoc, mul_comm (scalar b z), scalar_product hab hz, mul_one]

variable (d e : ComplexCharacterData) (a : Normalization)

/-- Raw or divided ambient family; validity justifies the derivative value. -/
def ambientFamily (ha : IsValid d e a) (z : ℂ) :
    KF 4 (source d e) →ₗ[ℂ] KF 4 (expanded e d) :=
  if a.divide then normalizedMap d e a.choices ha.1 z
  else RealInducedSwapRegularizedFamily.rawMap d e a.choices z

theorem ambientFamily_analytic (ha : IsValid d e a) (f : KF 4 (source d e)) :
    IsWeaklyAnalyticAt (fun z => ambientFamily d e a ha z f) 0 := by
  unfold ambientFamily
  split_ifs with h
  · exact normalizedMap_analytic d e a.choices ha.1 (ha.2 h) f
  · exact rawMap_analytic d e a.choices ha.1 f

theorem ambientFamily_exists_finite_range (ha : IsValid d e a)
    (f : KF 4 (source d e)) :
    ∃ S : Submodule ℂ (KF 4 (expanded e d)),
      FiniteDimensional ℂ S ∧ ∀ z, ambientFamily d e a ha z f ∈ S := by
  unfold ambientFamily
  split_ifs
  · exact normalizedMap_exists_finite_range d e a.choices ha.1 f
  · exact rawMap_exists_finite_range d e a.choices f

theorem ambientFamily_eq_generic (ha : IsValid d e a) {z : ℂ} (hz : z ≠ 0)
    (hg : IsGenericShift d e z) :
    ambientFamily d e a ha z = scalar a z •
      RealInducedSwapShifted.rawMap d e (genericFourCrossings hg) := by
  unfold ambientFamily scalar divisionOrder
  split_ifs with h
  · rw [normalizedMap, removeSimplePole_of_ne _ _ hz,
      rawMap_eq_scaled_generic d e a.choices ha.1 hz hg]
    simp only [pow_one, smul_smul, div_eq_mul_inv, mul_comm]
  · rw [rawMap_eq_scaled_generic d e a.choices ha.1 hz hg]
    simp only [pow_zero, div_one]

/-- A target-valued family at all parameters through the fixed retraction. -/
def targetFamily (ha : IsValid d e a) (z : ℂ) :
    KF 4 (source d e) →ₗ[ℂ] KF 4 (target d e) :=
  targetRetraction d e ∘ₗ ambientFamily d e a ha z

theorem targetFamily_analytic (ha : IsValid d e a) (f : KF 4 (source d e)) :
    IsWeaklyAnalyticAt (fun z => targetFamily d e a ha z f) 0 :=
  (ambientFamily_analytic d e a ha f).map (targetRetraction d e)

theorem targetFamily_exists_finite_range (ha : IsValid d e a)
    (f : KF 4 (source d e)) :
    ∃ S : Submodule ℂ (KF 4 (target d e)),
      FiniteDimensional ℂ S ∧ ∀ z, targetFamily d e a ha z f ∈ S := by
  obtain ⟨S, hS, hfS⟩ := ambientFamily_exists_finite_range d e a ha f
  let := hS
  exact ⟨S.map (targetRetraction d e), inferInstance,
    fun z => Submodule.mem_map_of_mem (hfS z)⟩

theorem targetFamily_eq_generic (ha : IsValid d e a) {z : ℂ} (hz : z ≠ 0)
    (hg : IsGenericShift d e z) :
    targetFamily d e a ha z = scalar a z •
      RealInducedSwapShifted.shiftedMap d e (genericFourCrossings hg) := by
  ext f : 1
  change targetRetraction d e (ambientFamily d e a ha z f) = _
  rw [ambientFamily_eq_generic d e a ha hz hg, LinearMap.smul_apply, map_smul]
  congr 1
  exact targetRetraction_inclusion d e
    (RealInducedSwapShifted.shiftedMap d e (genericFourCrossings hg) f)

set_option maxHeartbeats 1000000 in
/-- The opposite-shift scalar contributes a fixed nonzero sign. -/
theorem targetFamily_leftInverse
    (ha : IsValid d e a) (b : Normalization) (hb : IsValid e d b)
    (hab : Balanced a b)
    {L : Filter ℂ} [L.NeBot] (hL : L ≤ 𝓝 0)
    (hpath : ∀ᶠ z in L, z ≠ 0 ∧ IsGenericShift d e z) :
    Function.LeftInverse
      ((scalar b (-1))⁻¹ • targetFamily e d b hb 0)
      (targetFamily d e a ha 0) := by
  have hs : scalar b (-1) ≠ 0 := scalar_ne_zero b (by norm_num)
  have hinv : ∀ᶠ z in L, Function.LeftInverse
      ((scalar b (-1))⁻¹ • targetFamily e d b hb (-z))
      (targetFamily d e a ha z) := by
    filter_upwards [hpath] with z hz
    rw [targetFamily_eq_generic d e a ha hz.1 hz.2,
      targetFamily_eq_generic e d b hb (neg_ne_zero.mpr hz.1) hz.2.reverse]
    intro f
    simp only [LinearMap.smul_apply, map_smul, smul_smul]
    have hscalar : scalar a z * (scalar b (-1))⁻¹ * scalar b (-z) = 1 := by
      calc
        _ = (scalar b (-1))⁻¹ * (scalar b (-z) * scalar a z) := by ring
        _ = 1 := by rw [scalar_product_neg hab hz.1, inv_mul_cancel₀ hs]
    rw [← mul_assoc, hscalar, one_smul]
    exact shiftedMap_leftInverse (genericFourCrossings hz.2)
      (genericFourCrossings hz.2.reverse) (genericFourCrossings_areInverse hz.2) f
  have h := leftInverse_at_zero (targetFamily d e a ha)
    (fun z => (scalar b (-1))⁻¹ • targetFamily e d b hb (-z))
    (targetFamily_analytic d e a ha)
    (fun f => (weaklyAnalyticAt_neg (targetFamily_analytic e d b hb f)).map
      ((scalar b (-1))⁻¹ • LinearMap.id))
    (targetFamily_exists_finite_range d e a ha) hL hinv
  simpa only [neg_zero] using h

theorem targetFamily_zero_injective
    (ha : IsValid d e a) (b : Normalization) (hb : IsValid e d b)
    (hab : Balanced a b)
    {L : Filter ℂ} [L.NeBot] (hL : L ≤ 𝓝 0)
    (hpath : ∀ᶠ z in L, z ≠ 0 ∧ IsGenericShift d e z) :
    Function.Injective (targetFamily d e a ha 0) :=
  (targetFamily_leftInverse d e a ha b hb hab hL hpath).injective

/-- A scalar normalization retains generic compact equivariance. -/
theorem targetFamily_zero_rightTranslation
    (ha : IsValid d e a)
    {L : Filter ℂ} [L.NeBot] (hL : L ≤ 𝓝 0)
    (hpath : ∀ᶠ z in L, z ≠ 0 ∧ IsGenericShift d e z)
    (k : Matrix.unitaryGroup (Fin 4) ℝ) (f : KF 4 (source d e)) :
    targetFamily d e a ha 0 (realStandardRep 4 (source d e) k f) =
      realStandardRep 4 (target d e) k (targetFamily d e a ha 0 f) := by
  apply eq_of_weaklyAnalyticAt_eventuallyEq
    (targetFamily_analytic d e a ha (realStandardRep 4 (source d e) k f))
    ((targetFamily_analytic d e a ha f).map (realStandardRep 4 (target d e) k)) hL
  filter_upwards [hpath] with z hz
  rw [targetFamily_eq_generic d e a ha hz.1 hz.2]
  simp only [LinearMap.smul_apply, map_smul]
  congr 1
  exact RealInducedSwapShifted.shiftedMap_rightTranslation d e
    (genericFourCrossings hz.2) k f

end RealInducedSwapBalanced
end Langlands.Archimedean
