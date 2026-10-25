import Langlands.ClassFieldTheory.Local.GradedNormCoordinateSupport

/-! Divided traces and the linear trace coordinate from exact ideal bounds. -/
noncomputable section
namespace Langlands.LocalClassField.PrimeGradedNorm
open Langlands.PadicField.TopologicalData
universe u v
variable {p : ℕ} [Fact p.Prime]
variable (F : PadicField.{u} p) (L : PadicField.{v} p)
variable [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
variable [FiniteDimensional F.Carrier L.Carrier]

/-- The literal divided trace, integral by the supplied ideal-image bound. -/
def dividedTrace (πF : F.Carrier) (hF : F.canonicalTopologicalData.ord πF = 1)
    (m n : ℕ)
    (htrace : ∀ z : L.canonicalTopologicalData.Integers,
      z ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ m →
      ∃ a : F.canonicalTopologicalData.Integers,
        a ∈ IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ n ∧
        (a : F.Carrier) = Algebra.trace F.Carrier L.Carrier (z : L.Carrier))
    (z : L.canonicalTopologicalData.Integers)
    (hz : z ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ m) :
    F.canonicalTopologicalData.Integers :=
  F.canonicalTopologicalData.idealQuotient πF hF n
    (htrace z hz).choose (htrace z hz).choose_spec.1

omit [IsScalarTower (Padic p) F.Carrier L.Carrier] [FiniteDimensional F.Carrier L.Carrier] in
@[simp] theorem dividedTrace_coe (πF : F.Carrier) (hF : F.canonicalTopologicalData.ord πF = 1)
    (m n : ℕ) (htrace) (z : L.canonicalTopologicalData.Integers) (hz) :
    (dividedTrace F L πF hF m n htrace z hz : F.Carrier) =
      Algebra.trace F.Carrier L.Carrier (z : L.Carrier) / πF ^ n := by
  simp only [dividedTrace, idealQuotient_coe, (htrace z hz).choose_spec.2]

variable (htot : L.canonicalTopologicalData.ramificationIndex =
  Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex)
include htot

omit [FiniteDimensional F.Carrier L.Carrier] in
/-- The residue of a divided trace is multiplication by the literal trace coefficient. -/
theorem trace_coordinate_linear
    (πF : F.Carrier) (hF : F.canonicalTopologicalData.ord πF = 1)
    (πL : L.Carrier) (hL : L.canonicalTopologicalData.ord πL = 1)
    (m n : ℕ)
    (hnext : ∀ z : L.canonicalTopologicalData.Integers,
      z ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ (m + 1) →
      ∃ a : F.canonicalTopologicalData.Integers,
        a ∈ IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ (n + 1) ∧
        (a : F.Carrier) = Algebra.trace F.Carrier L.Carrier (z : L.Carrier))
    (c : L.canonicalTopologicalData.Integers) (b q : F.canonicalTopologicalData.Integers)
    (hb : (b : F.Carrier) = Algebra.trace F.Carrier L.Carrier (πL ^ m) / πF ^ n)
    (hq : (q : F.Carrier) = Algebra.trace F.Carrier L.Carrier (πL ^ m * (c : L.Carrier)) / πF ^ n) :
    relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue q) =
      relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue b) *
        L.canonicalTopologicalData.residue c := by
  obtain ⟨r, hr⟩ := (residue_bijective F L htot).2 (L.canonicalTopologicalData.residue c)
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  let δ := c - relativeIntegerMap F.canonicalTopologicalData L.canonicalTopologicalData a
  have hδ : δ ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    change L.canonicalTopologicalData.residue (c - relativeIntegerMap _ _ a) = 0
    rw [map_sub, ← relativeResidueMap_residue, hr, sub_self]
  let z := L.canonicalTopologicalData.coordinateUniformizer πL hL ^ m * δ
  have hz : z ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ (m + 1) := by
    rw [pow_succ]
    apply Ideal.mul_mem_mul
    · rw [L.canonicalTopologicalData.mem_maximalIdeal_pow_iff_coordinate_dvd πL hL]
    · exact hδ
  obtain ⟨A, hA, hAv⟩ := hnext z hz
  have hA0 := Ideal.pow_le_pow_right (Nat.le_succ n) hA
  let Q := F.canonicalTopologicalData.idealQuotient πF hF n A hA0
  have hQ0 : F.canonicalTopologicalData.residue Q = 0 :=
    (F.canonicalTopologicalData.residue_idealQuotient_eq_zero_iff πF hF n A hA0).mpr hA
  have ht : Algebra.trace F.Carrier L.Carrier (z : L.Carrier) =
      Algebra.trace F.Carrier L.Carrier (πL ^ m * (c : L.Carrier)) -
        (a : F.Carrier) * Algebra.trace F.Carrier L.Carrier (πL ^ m) := by
    simp only [z, Subring.coe_mul, Subring.coe_pow, coordinateUniformizer_coe]
    change Algebra.trace F.Carrier L.Carrier (πL ^ m * ((c : L.Carrier) -
      algebraMap F.Carrier L.Carrier (a : F.Carrier))) = _
    rw [mul_sub, map_sub]
    congr 1
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have he : Q = q - b * a := by
    apply Subtype.ext
    change (Q : F.Carrier) = (q : F.Carrier) - (b : F.Carrier) * (a : F.Carrier)
    rw [show (Q : F.Carrier) = (A : F.Carrier) / πF ^ n from rfl, hAv, ht, hb, hq]
    ring
  have hh : F.canonicalTopologicalData.residue q =
      F.canonicalTopologicalData.residue b * F.canonicalTopologicalData.residue a := by
    rw [he, map_sub, map_mul] at hQ0
    exact sub_eq_zero.mp hQ0
  rw [hh, map_mul, hr]

omit [FiniteDimensional F.Carrier L.Carrier] in
/-- Exact trace surjectivity forces the literal trace coefficient to have nonzero residue. -/
theorem trace_coefficient_ne_zero
    (πF : F.Carrier) (hF : F.canonicalTopologicalData.ord πF = 1)
    (πL : L.Carrier) (hL : L.canonicalTopologicalData.ord πL = 1)
    (m n : ℕ)
    (hnext : ∀ z : L.canonicalTopologicalData.Integers,
      z ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ (m + 1) →
      ∃ a : F.canonicalTopologicalData.Integers,
        a ∈ IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ (n + 1) ∧
        (a : F.Carrier) = Algebra.trace F.Carrier L.Carrier (z : L.Carrier))
    (honto : ∀ a : F.canonicalTopologicalData.Integers,
      a ∈ IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ n →
      ∃ z : L.canonicalTopologicalData.Integers,
        z ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ m ∧
        Algebra.trace F.Carrier L.Carrier (z : L.Carrier) = (a : F.Carrier))
    (b : F.canonicalTopologicalData.Integers)
    (hb : (b : F.Carrier) = Algebra.trace F.Carrier L.Carrier (πL ^ m) / πF ^ n) :
    F.canonicalTopologicalData.residue b ≠ 0 := by
  have hπ : F.canonicalTopologicalData.coordinateUniformizer πF hF ^ n ∈
      IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ n := by
    rw [F.canonicalTopologicalData.mem_maximalIdeal_pow_iff_coordinate_dvd πF hF]
  obtain ⟨z, hz, hzt⟩ := honto _ hπ
  let c := L.canonicalTopologicalData.idealQuotient πL hL m z hz
  have hc : πL ^ m * (c : L.Carrier) = (z : L.Carrier) := by
    have h := congrArg (fun a : L.canonicalTopologicalData.Integers => (a : L.Carrier))
      (L.canonicalTopologicalData.uniformizer_pow_mul_idealQuotient πL hL m z hz)
    simpa only [Subring.coe_mul, Subring.coe_pow, coordinateUniformizer_coe] using h
  have hq : (1 : F.Carrier) =
      Algebra.trace F.Carrier L.Carrier (πL ^ m * (c : L.Carrier)) / πF ^ n := by
    rw [hc, hzt]
    simp only [Subring.coe_pow, coordinateUniformizer_coe]
    exact (div_self (pow_ne_zero _ (F.canonicalTopologicalData.coordinateUniformizer_ne_zero πF hF))).symm
  have he := trace_coordinate_linear F L htot πF hF πL hL m n hnext c b 1 hb hq
  intro hb0
  simp only [map_one, hb0, map_zero, zero_mul] at he
  exact one_ne_zero he

omit [FiniteDimensional F.Carrier L.Carrier] in
/-- The trace term for a positive unit coordinate, with its literal coefficient. -/
theorem trace_term_coordinate
    (πF : F.Carrier) (hF : F.canonicalTopologicalData.ord πF = 1)
    (πL : L.Carrier) (hL : L.canonicalTopologicalData.ord πL = 1)
    (m n : ℕ)
    (hnext : ∀ z : L.canonicalTopologicalData.Integers,
      z ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ (m + 1) →
      ∃ a : F.canonicalTopologicalData.Integers,
        a ∈ IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ (n + 1) ∧
        (a : F.Carrier) = Algebra.trace F.Carrier L.Carrier (z : L.Carrier))
    (x : L.canonicalTopologicalData.unitFiltration m)
    (b q : F.canonicalTopologicalData.Integers)
    (hb : (b : F.Carrier) = Algebra.trace F.Carrier L.Carrier (πL ^ m) / πF ^ n)
    (hq : (q : F.Carrier) = Algebra.trace F.Carrier L.Carrier
      (((x : L.Carrierˣ) : L.Carrier) - 1) / πF ^ n) :
    relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue q) =
      relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue b) *
        L.canonicalTopologicalData.residue (L.canonicalTopologicalData.unitCoefficient πL hL m x) := by
  apply trace_coordinate_linear F L htot πF hF πL hL m n hnext _ b q hb
  have hx := congrArg (fun z : L.canonicalTopologicalData.Integers => (z : L.Carrier))
    (L.canonicalTopologicalData.coordinateUniformizer_pow_mul_coefficient πL hL m x)
  change (L.canonicalTopologicalData.coordinateUniformizer πL hL : L.Carrier) ^ m *
    (L.canonicalTopologicalData.unitCoefficient πL hL m x : L.Carrier) =
    ((L.canonicalTopologicalData.filtrationIntegerUnit m x : L.canonicalTopologicalData.Integers) : L.Carrier) - 1 at hx
  rw [coordinateUniformizer_coe, filtrationIntegerUnit_coe] at hx
  rw [hx]
  exact hq

end Langlands.LocalClassField.PrimeGradedNorm
