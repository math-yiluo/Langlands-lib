import Langlands.ClassFieldTheory.Local.PrimeGradedNormSupport

/-! Literal ideal-power quotients and the nonzero norm coefficient. -/
noncomputable section
namespace Langlands.PadicField.TopologicalData
universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)
variable (π : F.Carrier) (hπ : T.ord π = 1)
include hπ

/-- Integrality of division by the supplied uniformizer power. -/
theorem idealQuotient_integral (n : ℕ) (a : T.Integers)
    (ha : a ∈ IsLocalRing.maximalIdeal T.Integers ^ n) :
    (a : F.Carrier) / π ^ n ∈ T.Integers := by
  obtain ⟨b, hb⟩ := (T.mem_maximalIdeal_pow_iff_coordinate_dvd π hπ n a).mp ha
  have he := congrArg (fun z : T.Integers => (z : F.Carrier)) hb
  change (a : F.Carrier) = (T.coordinateUniformizer π hπ : F.Carrier) ^ n * (b : F.Carrier) at he
  rw [T.coordinateUniformizer_coe] at he
  rw [he, mul_div_cancel_left₀ _ (pow_ne_zero _ (T.coordinateUniformizer_ne_zero π hπ))]
  exact b.property

/-- The literal quotient of an ideal-power element by a uniformizer power. -/
def idealQuotient (n : ℕ) (a : T.Integers)
    (ha : a ∈ IsLocalRing.maximalIdeal T.Integers ^ n) : T.Integers :=
  ⟨(a : F.Carrier) / π ^ n, T.idealQuotient_integral π hπ n a ha⟩

@[simp] theorem idealQuotient_coe (n : ℕ) (a : T.Integers)
    (ha : a ∈ IsLocalRing.maximalIdeal T.Integers ^ n) :
    (T.idealQuotient π hπ n a ha : F.Carrier) = (a : F.Carrier) / π ^ n := rfl

theorem uniformizer_pow_mul_idealQuotient (n : ℕ) (a : T.Integers)
    (ha : a ∈ IsLocalRing.maximalIdeal T.Integers ^ n) :
    T.coordinateUniformizer π hπ ^ n * T.idealQuotient π hπ n a ha = a := by
  apply Subtype.ext
  change (T.coordinateUniformizer π hπ : F.Carrier) ^ n *
    (T.idealQuotient π hπ n a ha : F.Carrier) = (a : F.Carrier)
  rw [T.coordinateUniformizer_coe, T.idealQuotient_coe]
  exact mul_div_cancel₀ _ (pow_ne_zero _ (T.coordinateUniformizer_ne_zero π hπ))

theorem residue_idealQuotient_eq_zero_iff (n : ℕ) (a : T.Integers)
    (ha : a ∈ IsLocalRing.maximalIdeal T.Integers ^ n) :
    T.residue (T.idealQuotient π hπ n a ha) = 0 ↔
      a ∈ IsLocalRing.maximalIdeal T.Integers ^ (n + 1) := by
  rw [IsLocalRing.residue_eq_zero_iff, T.maximalIdeal_eq_span_coordinateUniformizer π hπ,
    Ideal.mem_span_singleton, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  conv_rhs => rw [← T.uniformizer_pow_mul_idealQuotient π hπ n a ha]
  rw [pow_succ,
    mul_dvd_mul_iff_left (pow_ne_zero _ (T.coordinateUniformizer_integer_ne_zero π hπ))]

omit π hπ in
theorem residue_ne_zero_of_ord_eq_zero (a : T.Integers) (ha : (a : F.Carrier) ≠ 0)
    (ho : T.ord (a : F.Carrier) = 0) : T.residue a ≠ 0 := by
  have hi : (a : F.Carrier)⁻¹ ∈ T.Integers := by
    apply (T.normalizedAbs_le_one_iff_mem_integers _).mp
    rw [T.normalizedAbs_of_ne_zero (inv_ne_zero ha), T.ord_inv, ho]
    simp
  apply (IsLocalRing.residue_ne_zero_iff_isUnit a).mpr
  refine ⟨⟨a, ⟨(a : F.Carrier)⁻¹, hi⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ ha)
  · exact Subtype.ext (inv_mul_cancel₀ ha)

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalClassField.PrimeGradedNorm
open Langlands.PadicField.TopologicalData
universe u v
variable {p : ℕ} [Fact p.Prime]
variable (F : PadicField.{u} p) (L : PadicField.{v} p)
variable [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
variable [FiniteDimensional F.Carrier L.Carrier]
variable (htot : L.canonicalTopologicalData.ramificationIndex =
  Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex)
include htot

omit htot in
@[simp] theorem integerNorm_mul (x y : L.canonicalTopologicalData.Integers) :
    integerNorm F L (x * y) = integerNorm F L x * integerNorm F L y := by
  apply Subtype.ext
  exact map_mul (Algebra.norm F.Carrier) (x : L.Carrier) (y : L.Carrier)

omit htot in
@[simp] theorem integerNorm_pow (x : L.canonicalTopologicalData.Integers) (n : ℕ) :
    integerNorm F L (x ^ n) = integerNorm F L x ^ n := by
  apply Subtype.ext
  exact map_pow (Algebra.norm F.Carrier) (x : L.Carrier) n

theorem integerNorm_mem_pow (n : ℕ) (x : L.canonicalTopologicalData.Integers)
    (hx : x ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ n) :
    integerNorm F L x ∈ IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ n := by
  let π := L.canonicalTopologicalData.uniformizer
  have hπ : L.canonicalTopologicalData.ord π = 1 := L.canonicalTopologicalData.ord_uniformizer
  have hN : F.canonicalTopologicalData.ord (Algebra.norm F.Carrier π) = 1 := by
    rw [ord_norm F L htot, hπ]
  obtain ⟨a, ha⟩ := (L.canonicalTopologicalData.mem_maximalIdeal_pow_iff_coordinate_dvd π hπ n x).mp hx
  rw [ha, integerNorm_mul, integerNorm_pow]
  have he : integerNorm F L (L.canonicalTopologicalData.coordinateUniformizer π hπ) =
      F.canonicalTopologicalData.coordinateUniformizer (Algebra.norm F.Carrier π) hN := by
    apply Subtype.ext
    simp
  rw [he, F.canonicalTopologicalData.mem_maximalIdeal_pow_iff_coordinate_dvd (Algebra.norm F.Carrier π) hN]
  exact dvd_mul_right _ _

/-- The norm coefficient is the literal quotient and has nonzero residue. -/
theorem norm_coefficient (πF : F.Carrier) (hF : F.canonicalTopologicalData.ord πF = 1)
    (πL : L.Carrier) (hL : L.canonicalTopologicalData.ord πL = 1) (n : ℕ) :
    ∃ a : F.canonicalTopologicalData.Integers,
      (a : F.Carrier) = Algebra.norm F.Carrier πL ^ n / πF ^ n ∧
      F.canonicalTopologicalData.residue a ≠ 0 := by
  let z := integerNorm F L (L.canonicalTopologicalData.coordinateUniformizer πL hL ^ n)
  have hz : z ∈ IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ n := by
    apply integerNorm_mem_pow F L htot
    rw [L.canonicalTopologicalData.mem_maximalIdeal_pow_iff_coordinate_dvd πL hL]
  let a := F.canonicalTopologicalData.idealQuotient πF hF n z hz
  have ha : (a : F.Carrier) = Algebra.norm F.Carrier πL ^ n / πF ^ n := by
    simp [a, z]
  refine ⟨a, ha, ?_⟩
  have hN : Algebra.norm F.Carrier πL ≠ 0 :=
    (Algebra.norm_ne_zero_iff).mpr (L.canonicalTopologicalData.coordinateUniformizer_ne_zero πL hL)
  have hF0 := F.canonicalTopologicalData.coordinateUniformizer_ne_zero πF hF
  apply F.canonicalTopologicalData.residue_ne_zero_of_ord_eq_zero a
  · rw [ha]
    exact div_ne_zero (pow_ne_zero _ hN) (pow_ne_zero _ hF0)
  · rw [ha, div_eq_mul_inv,
      F.canonicalTopologicalData.ord_mul (pow_ne_zero _ hN) (inv_ne_zero (pow_ne_zero _ hF0)),
      F.canonicalTopologicalData.ord_inv, ← zpow_natCast, ← zpow_natCast,
      F.canonicalTopologicalData.ord_zpow, F.canonicalTopologicalData.ord_zpow,
      ord_norm F L htot, hL, hF]
    ring

variable [IsGalois F.Carrier L.Carrier]

/-- The norm term in the positive unit-coordinate calculation. -/
theorem norm_term_coordinate (πF : F.Carrier)
    (πL : L.Carrier) (hL : L.canonicalTopologicalData.ord πL = 1) (n : ℕ)
    (x : L.canonicalTopologicalData.unitFiltration n)
    (a q : F.canonicalTopologicalData.Integers)
    (ha : (a : F.Carrier) = Algebra.norm F.Carrier πL ^ n / πF ^ n)
    (hq : (q : F.Carrier) =
      Algebra.norm F.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) / πF ^ n) :
    relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData
      (F.canonicalTopologicalData.residue q) =
    relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData
      (F.canonicalTopologicalData.residue a) *
      L.canonicalTopologicalData.residue (L.canonicalTopologicalData.unitCoefficient πL hL n x) ^
        Module.finrank F.Carrier L.Carrier := by
  have hx := congrArg (fun z : L.canonicalTopologicalData.Integers => (z : L.Carrier))
    (L.canonicalTopologicalData.coordinateUniformizer_pow_mul_coefficient πL hL n x)
  change (L.canonicalTopologicalData.coordinateUniformizer πL hL : L.Carrier) ^ n *
    (L.canonicalTopologicalData.unitCoefficient πL hL n x : L.Carrier) =
    ((L.canonicalTopologicalData.filtrationIntegerUnit n x : L.canonicalTopologicalData.Integers) : L.Carrier) - 1 at hx
  rw [L.canonicalTopologicalData.coordinateUniformizer_coe,
    L.canonicalTopologicalData.filtrationIntegerUnit_coe] at hx
  have he : q = a * integerNorm F L (L.canonicalTopologicalData.unitCoefficient πL hL n x) := by
    apply Subtype.ext
    change (q : F.Carrier) = (a : F.Carrier) *
      (integerNorm F L (L.canonicalTopologicalData.unitCoefficient πL hL n x) : F.Carrier)
    rw [hq, ← hx, map_mul, map_pow, ha, integerNorm_coe]
    ring
  rw [he, map_mul, map_mul, residue_norm F L htot]

end Langlands.LocalClassField.PrimeGradedNorm
