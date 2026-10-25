import Langlands.ClassFieldTheory.Local.PrimeGradedNormFiltrationSupport
import Langlands.ClassFieldTheory.Local.PrimeGradedNormBelowBreakStatement

/-! Conditional below-break coordinate assembly with literal coefficients. -/
noncomputable section
namespace Langlands.LocalClassField.PrimeGradedNorm
open Langlands.PadicField.TopologicalData
universe u v
variable {p : ℕ} [Fact p.Prime]
variable (F : PadicField.{u} p) (L : PadicField.{v} p)
variable [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
variable [FiniteDimensional F.Carrier L.Carrier]

/-- Divide the actual expansion by the target uniformizer and then reduce. -/
theorem coordinate_of_expansion
    (πF : F.Carrier) (hF : F.canonicalTopologicalData.ord πF = 1)
    (m n : ℕ) (x : L.canonicalTopologicalData.unitFiltration m)
    (y : F.canonicalTopologicalData.unitFiltration n)
    (hxy : (y : F.Carrierˣ) = normUnits F.Carrier L.Carrier (x : L.Carrierˣ))
    (z : L.canonicalTopologicalData.Integers) (a b c : F.canonicalTopologicalData.Integers)
    (ha : (a : F.Carrier) = Algebra.trace F.Carrier L.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) / πF ^ n)
    (hb : (b : F.Carrier) = Algebra.norm F.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) / πF ^ n)
    (hc : (c : F.Carrier) = Algebra.trace F.Carrier L.Carrier (z : L.Carrier) / πF ^ n)
    (hex : Algebra.norm F.Carrier ((x : L.Carrierˣ) : L.Carrier) - 1 -
      Algebra.trace F.Carrier L.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) -
      Algebra.norm F.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) =
      Algebra.trace F.Carrier L.Carrier (z : L.Carrier)) :
    relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData
      (F.canonicalTopologicalData.residue (F.canonicalTopologicalData.unitCoefficient πF hF n y)) =
    relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue a) +
    relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue b) +
    relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue c) := by
  have hy : ((y : F.Carrierˣ) : F.Carrier) = Algebra.norm F.Carrier ((x : L.Carrierˣ) : L.Carrier) :=
    congrArg (fun z : F.Carrierˣ => (z : F.Carrier)) hxy
  have hh : Algebra.norm F.Carrier ((x : L.Carrierˣ) : L.Carrier) - 1 =
      Algebra.trace F.Carrier L.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) +
      Algebra.norm F.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) +
      Algebra.trace F.Carrier L.Carrier (z : L.Carrier) := by
    linear_combination hex
  have he : F.canonicalTopologicalData.unitCoefficient πF hF n y = a + b + c := by
    apply Subtype.ext
    change (F.canonicalTopologicalData.unitCoefficient πF hF n y : F.Carrier) = (a : F.Carrier) + (b : F.Carrier) + (c : F.Carrier)
    rw [F.canonicalTopologicalData.unitCoefficient_coe, hy, hh, ha, hb, hc]
    ring
  simp only [he, map_add]

variable [IsGalois F.Carrier L.Carrier]
variable (htot : L.canonicalTopologicalData.ramificationIndex =
  Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex)
include htot

/-- Below the positive break only the norm term survives reduction. -/
theorem below_break_of_arithmetic
    (htrace : PrimeRamifiedTraceIdeals.{u,v}) (hexpansion : PrimeNormTraceExpansion.{u,v})
    (hell : Nat.Prime (Module.finrank F.Carrier L.Carrier)) (t : ℕ)
    (hpat : ∀ i : ℕ, Ramification.Padic.lowerRamificationGroup L.canonicalTopologicalData F.Carrier i =
      if i ≤ t then ⊤ else ⊥)
    (πF : F.Carrier) (hF : F.canonicalTopologicalData.ord πF = 1)
    (πL : L.Carrier) (hL : L.canonicalTopologicalData.ord πL = 1)
    (n : ℕ) (hn : 0 < n) (hnt : n < t) :
    ∃ a : F.canonicalTopologicalData.Integers,
      (a : F.Carrier) = Algebra.norm F.Carrier πL ^ n / πF ^ n ∧
      F.canonicalTopologicalData.residue a ≠ 0 ∧
      ∀ (x : L.canonicalTopologicalData.unitFiltration n) (y : F.canonicalTopologicalData.unitFiltration n),
        (y : F.Carrierˣ) = normUnits F.Carrier L.Carrier (x : L.Carrierˣ) →
        relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData
          (F.canonicalTopologicalData.residue (F.canonicalTopologicalData.unitCoefficient πF hF n y)) =
        relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue a) *
          L.canonicalTopologicalData.residue (L.canonicalTopologicalData.unitCoefficient πL hL n x) ^ p := by
  obtain ⟨a, ha, ha0⟩ := norm_coefficient F L htot πF hF πL hL n
  refine ⟨a, ha, ha0, ?_⟩
  intro x y hxy
  let δ : L.canonicalTopologicalData.Integers :=
    (L.canonicalTopologicalData.filtrationIntegerUnit n x : L.canonicalTopologicalData.Integers) - 1
  have hd : δ ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ n :=
    (L.canonicalTopologicalData.mem_congruenceUnits_iff n _).mp
      (L.canonicalTopologicalData.filtrationIntegerUnit_mem n x)
  have hδ : (δ : L.Carrier) = ((x : L.Carrierˣ) : L.Carrier) - 1 := by
    change ((L.canonicalTopologicalData.filtrationIntegerUnit n x : L.canonicalTopologicalData.Integers) : L.Carrier) - 1 = _
    rw [L.canonicalTopologicalData.filtrationIntegerUnit_coe]
  obtain ⟨z, hz, hex⟩ := hexpansion p F L hell htot n δ hd
  obtain ⟨A, hA, hAt⟩ := (htrace p F L hell htot t hpat n
    (Algebra.trace F.Carrier L.Carrier (δ : L.Carrier))).mp ⟨δ, hd, rfl⟩
  obtain ⟨C, hC, hCt⟩ := (htrace p F L hell htot t hpat (2 * n)
    (Algebra.trace F.Carrier L.Carrier (z : L.Carrier))).mp ⟨z, hz, rfl⟩
  have hbound : n + 1 ≤ ((t + 1) * (Module.finrank F.Carrier L.Carrier - 1) + n) /
      Module.finrank F.Carrier L.Carrier := by
    apply (Nat.le_div_iff_mul_le hell.pos).mpr
    have hp := hell.two_le
    have he : Module.finrank F.Carrier L.Carrier - 1 + 1 = Module.finrank F.Carrier L.Carrier := by omega
    have hh := Nat.mul_le_mul_right (Module.finrank F.Carrier L.Carrier - 1) (show n + 2 ≤ t + 1 by omega)
    nlinarith
  have hA1 : A ∈ IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ (n + 1) :=
    Ideal.pow_le_pow_right hbound hA
  have hC1 : C ∈ IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ (n + 1) :=
    Ideal.pow_le_pow_right (hbound.trans (Nat.div_le_div_right (by omega))) hC
  have hA0 := Ideal.pow_le_pow_right (Nat.le_succ n) hA1
  have hC0 := Ideal.pow_le_pow_right (Nat.le_succ n) hC1
  have hB0 := integerNorm_mem_pow F L htot n δ hd
  let qA := F.canonicalTopologicalData.idealQuotient πF hF n A hA0
  let qB := F.canonicalTopologicalData.idealQuotient πF hF n (integerNorm F L δ) hB0
  let qC := F.canonicalTopologicalData.idealQuotient πF hF n C hC0
  have hqA : F.canonicalTopologicalData.residue qA = 0 :=
    (F.canonicalTopologicalData.residue_idealQuotient_eq_zero_iff πF hF n A hA0).mpr hA1
  have hqC : F.canonicalTopologicalData.residue qC = 0 :=
    (F.canonicalTopologicalData.residue_idealQuotient_eq_zero_iff πF hF n C hC0).mpr hC1
  have hqAv : (qA : F.Carrier) = Algebra.trace F.Carrier L.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) / πF ^ n := by
    simp only [qA, idealQuotient_coe, hAt, hδ]
  have hqBv : (qB : F.Carrier) = Algebra.norm F.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) / πF ^ n := by
    simp only [qB, idealQuotient_coe, integerNorm_coe, hδ]
  have hqCv : (qC : F.Carrier) = Algebra.trace F.Carrier L.Carrier (z : L.Carrier) / πF ^ n := by
    simp only [qC, idealQuotient_coe, hCt]
  have he := coordinate_of_expansion F L πF hF n n x y hxy z qA qB qC hqAv hqBv hqCv
    (by simpa only [hδ, add_sub_cancel] using hex)
  rw [hqA, hqC, map_zero, zero_add, add_zero] at he
  rw [he, norm_term_coordinate F L htot πF πL hL n x a qB ha hqBv,
    degree_eq_prime_of_positive_break F L htot hell t (by omega) hpat]

end Langlands.LocalClassField.PrimeGradedNorm

namespace Langlands.LocalClassField
/-- Exact isolated conditional below-break proposition. -/
theorem primeGradedNormBelowBreakFromArithmetic.{u,v} : PrimeGradedNormBelowBreakFromArithmetic.{u,v} := by
  intro p _ F L _ _ _ _ htot htrace hexpansion hell t hpat πF hF πL hL n hn hnt
  exact PrimeGradedNorm.below_break_of_arithmetic F L htot htrace hexpansion hell t hpat πF hF πL hL n hn hnt
end Langlands.LocalClassField
