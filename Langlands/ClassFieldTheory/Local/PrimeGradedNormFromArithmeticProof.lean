import Langlands.ClassFieldTheory.Local.PrimeGradedNormBelowBreakSupport
import Langlands.ClassFieldTheory.Local.GradedTraceCoordinateSupport
import Langlands.ClassFieldTheory.Local.PrimeGradedNormFromArithmeticStatement

noncomputable section
namespace Langlands.LocalClassField.PrimeGradedNorm
open Langlands.PadicField.TopologicalData
universe u v

/-- The exact and next trace indices at and above the break. -/
theorem trace_indices (ell t n : ℕ) (hell : 0 < ell) (htn : t ≤ n) :
    let m := if n ≤ t then n else t + ell * (n - t)
    ((t + 1) * (ell - 1) + m) / ell = n ∧
      ((t + 1) * (ell - 1) + (m + 1)) / ell = n + 1 := by
  have he : ell - 1 + 1 = ell := by omega
  have hm : (if n ≤ t then n else t + ell * (n - t)) = t + ell * (n - t) := by
    split_ifs with h
    · have hn : n = t := by omega
      simp [hn]
    · rfl
  rw [hm]
  have hn : t + (n - t) = n := by omega
  constructor <;> apply Nat.div_eq_of_lt_le <;> nlinarith

variable {p : ℕ} [Fact p.Prime]
variable (F : PadicField.{u} p) (L : PadicField.{v} p)
variable [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
variable [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier]
variable (htot : L.canonicalTopologicalData.ramificationIndex =
  Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex)
variable (htrace : PrimeRamifiedTraceIdeals.{u,v})
variable (hell : Nat.Prime (Module.finrank F.Carrier L.Carrier)) (t : ℕ)
variable (hpat : ∀ i : ℕ, Ramification.Padic.lowerRamificationGroup L.canonicalTopologicalData F.Carrier i =
  if i ≤ t then ⊤ else ⊥)
include htot htrace hell hpat

/-- Extract the forward ideal bound from the exact trace-image hypothesis. -/
theorem trace_bound (m n : ℕ)
    (hbound : n ≤ ((t + 1) * (Module.finrank F.Carrier L.Carrier - 1) + m) /
      Module.finrank F.Carrier L.Carrier)
    (z : L.canonicalTopologicalData.Integers)
    (hz : z ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ m) :
    ∃ a : F.canonicalTopologicalData.Integers,
      a ∈ IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ n ∧
      (a : F.Carrier) = Algebra.trace F.Carrier L.Carrier (z : L.Carrier) := by
  obtain ⟨a, ha, hat⟩ := (htrace p F L hell htot t hpat m
    (Algebra.trace F.Carrier L.Carrier (z : L.Carrier))).mp ⟨z, hz, rfl⟩
  exact ⟨a, Ideal.pow_le_pow_right hbound ha, hat⟩

/-- The literal trace coefficient is integral and nonzero at the exact trace index. -/
theorem trace_coefficient_of_arithmetic
    (πF : F.Carrier) (hF : F.canonicalTopologicalData.ord πF = 1)
    (πL : L.Carrier) (hL : L.canonicalTopologicalData.ord πL = 1)
    (m n : ℕ)
    (hindex : ((t + 1) * (Module.finrank F.Carrier L.Carrier - 1) + m) /
      Module.finrank F.Carrier L.Carrier = n)
    (hnextindex : n + 1 ≤ ((t + 1) * (Module.finrank F.Carrier L.Carrier - 1) + (m + 1)) /
      Module.finrank F.Carrier L.Carrier) :
    ∃ b : F.canonicalTopologicalData.Integers,
      (b : F.Carrier) = Algebra.trace F.Carrier L.Carrier (πL ^ m) / πF ^ n ∧
      F.canonicalTopologicalData.residue b ≠ 0 := by
  have hπ : L.canonicalTopologicalData.coordinateUniformizer πL hL ^ m ∈
      IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ m := by
    rw [L.canonicalTopologicalData.mem_maximalIdeal_pow_iff_coordinate_dvd πL hL]
  let b := dividedTrace F L πF hF m n
    (trace_bound F L htot htrace hell t hpat m n hindex.ge) _ hπ
  have hb : (b : F.Carrier) = Algebra.trace F.Carrier L.Carrier (πL ^ m) / πF ^ n := by
    simp [b]
  refine ⟨b, hb, trace_coefficient_ne_zero F L htot πF hF πL hL m n
    (trace_bound F L htot htrace hell t hpat (m + 1) (n + 1) hnextindex) ?_ b hb⟩
  intro a ha
  apply (htrace p F L hell htot t hpat m (a : F.Carrier)).mpr
  exact ⟨a, hindex ▸ ha, rfl⟩

/-- At a positive break the trace and norm terms both survive. -/
theorem critical_of_arithmetic (hexpansion : PrimeNormTraceExpansion.{u,v})
    (πF : F.Carrier) (hF : F.canonicalTopologicalData.ord πF = 1)
    (πL : L.Carrier) (hL : L.canonicalTopologicalData.ord πL = 1)
    (ht : 0 < t) :
    ∃ a b : F.canonicalTopologicalData.Integers,
      (a : F.Carrier) = Algebra.norm F.Carrier πL ^ t / πF ^ t ∧
      (b : F.Carrier) = Algebra.trace F.Carrier L.Carrier (πL ^ t) / πF ^ t ∧
      F.canonicalTopologicalData.residue a ≠ 0 ∧ F.canonicalTopologicalData.residue b ≠ 0 ∧
      ∀ (x : L.canonicalTopologicalData.unitFiltration t) (y : F.canonicalTopologicalData.unitFiltration t),
        (y : F.Carrierˣ) = normUnits F.Carrier L.Carrier (x : L.Carrierˣ) →
        relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData
          (F.canonicalTopologicalData.residue (F.canonicalTopologicalData.unitCoefficient πF hF t y)) =
        relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue a) *
          L.canonicalTopologicalData.residue (L.canonicalTopologicalData.unitCoefficient πL hL t x) ^ p +
        relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue b) *
          L.canonicalTopologicalData.residue (L.canonicalTopologicalData.unitCoefficient πL hL t x) := by
  have hi := trace_indices (Module.finrank F.Carrier L.Carrier) t t hell.pos le_rfl
  simp only [le_refl, ↓reduceIte] at hi
  obtain ⟨a, ha, ha0⟩ := norm_coefficient F L htot πF hF πL hL t
  obtain ⟨b, hb, hb0⟩ := trace_coefficient_of_arithmetic F L htot htrace hell t hpat
    πF hF πL hL t t hi.1 hi.2.ge
  refine ⟨a, b, ha, hb, ha0, hb0, ?_⟩
  intro x y hxy
  let δ : L.canonicalTopologicalData.Integers :=
    (L.canonicalTopologicalData.filtrationIntegerUnit t x : L.canonicalTopologicalData.Integers) - 1
  have hd : δ ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ t :=
    (L.canonicalTopologicalData.mem_congruenceUnits_iff t _).mp
      (L.canonicalTopologicalData.filtrationIntegerUnit_mem t x)
  have hδ : (δ : L.Carrier) = ((x : L.Carrierˣ) : L.Carrier) - 1 := by
    change ((L.canonicalTopologicalData.filtrationIntegerUnit t x : L.canonicalTopologicalData.Integers) : L.Carrier) - 1 = _
    rw [L.canonicalTopologicalData.filtrationIntegerUnit_coe]
  obtain ⟨z, hz, hex⟩ := hexpansion p F L hell htot t δ hd
  have hrem : t + 1 ≤ ((t + 1) * (Module.finrank F.Carrier L.Carrier - 1) + 2 * t) /
      Module.finrank F.Carrier L.Carrier :=
    hi.2.ge.trans (Nat.div_le_div_right (by omega))
  obtain ⟨A, hA, hAt⟩ := trace_bound F L htot htrace hell t hpat t t hi.1.ge δ hd
  obtain ⟨C, hC, hCt⟩ := trace_bound F L htot htrace hell t hpat (2 * t) (t + 1) hrem z hz
  have hC0 := Ideal.pow_le_pow_right (Nat.le_succ t) hC
  have hB := integerNorm_mem_pow F L htot t δ hd
  let qA := F.canonicalTopologicalData.idealQuotient πF hF t A hA
  let qB := F.canonicalTopologicalData.idealQuotient πF hF t (integerNorm F L δ) hB
  let qC := F.canonicalTopologicalData.idealQuotient πF hF t C hC0
  have hqC : F.canonicalTopologicalData.residue qC = 0 :=
    (F.canonicalTopologicalData.residue_idealQuotient_eq_zero_iff πF hF t C hC0).mpr hC
  have hqAv : (qA : F.Carrier) = Algebra.trace F.Carrier L.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) / πF ^ t := by
    simp only [qA, idealQuotient_coe, hAt, hδ]
  have hqBv : (qB : F.Carrier) = Algebra.norm F.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) / πF ^ t := by
    simp only [qB, idealQuotient_coe, integerNorm_coe, hδ]
  have hqCv : (qC : F.Carrier) = Algebra.trace F.Carrier L.Carrier (z : L.Carrier) / πF ^ t := by
    simp only [qC, idealQuotient_coe, hCt]
  have he := coordinate_of_expansion F L πF hF t t x y hxy z qA qB qC hqAv hqBv hqCv
    (by simpa only [hδ, add_sub_cancel] using hex)
  rw [hqC, map_zero, add_zero] at he
  rw [he, norm_term_coordinate F L htot πF πL hL t x a qB ha hqBv,
    trace_term_coordinate F L htot πF hF πL hL t t
      (trace_bound F L htot htrace hell t hpat (t + 1) (t + 1) hi.2.ge) x b qA hb hqAv,
    degree_eq_prime_of_positive_break F L htot hell t ht hpat, add_comm]

/-- Above the break only the trace contribution survives reduction. -/
theorem above_of_arithmetic (hexpansion : PrimeNormTraceExpansion.{u,v})
    (πF : F.Carrier) (hF : F.canonicalTopologicalData.ord πF = 1)
    (πL : L.Carrier) (hL : L.canonicalTopologicalData.ord πL = 1)
    (n : ℕ) (hnt : t < n) :
    let m := if n ≤ t then n else t + Module.finrank F.Carrier L.Carrier * (n - t)
    ∃ b : F.canonicalTopologicalData.Integers,
      (b : F.Carrier) = Algebra.trace F.Carrier L.Carrier (πL ^ m) / πF ^ n ∧
      F.canonicalTopologicalData.residue b ≠ 0 ∧
      ∀ (x : L.canonicalTopologicalData.unitFiltration m) (y : F.canonicalTopologicalData.unitFiltration n),
        (y : F.Carrierˣ) = normUnits F.Carrier L.Carrier (x : L.Carrierˣ) →
        relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData
          (F.canonicalTopologicalData.residue (F.canonicalTopologicalData.unitCoefficient πF hF n y)) =
        relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue b) *
          L.canonicalTopologicalData.residue (L.canonicalTopologicalData.unitCoefficient πL hL m x) := by
  let m := if n ≤ t then n else t + Module.finrank F.Carrier L.Carrier * (n - t)
  have hi := trace_indices (Module.finrank F.Carrier L.Carrier) t n hell.pos hnt.le
  have hnm : n + 1 ≤ m := by
    dsimp only [m]
    simp only [show ¬n ≤ t by omega, ↓reduceIte]
    have hp := hell.two_le
    have hn : t + (n - t) = n := by omega
    nlinarith [Nat.mul_le_mul_right (n - t) hp]
  obtain ⟨b, hb, hb0⟩ := trace_coefficient_of_arithmetic F L htot htrace hell t hpat
    πF hF πL hL m n hi.1 hi.2.ge
  refine ⟨b, hb, hb0, ?_⟩
  intro x y hxy
  let δ : L.canonicalTopologicalData.Integers :=
    (L.canonicalTopologicalData.filtrationIntegerUnit m x : L.canonicalTopologicalData.Integers) - 1
  have hd : δ ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ m :=
    (L.canonicalTopologicalData.mem_congruenceUnits_iff m _).mp
      (L.canonicalTopologicalData.filtrationIntegerUnit_mem m x)
  have hδ : (δ : L.Carrier) = ((x : L.Carrierˣ) : L.Carrier) - 1 := by
    change ((L.canonicalTopologicalData.filtrationIntegerUnit m x : L.canonicalTopologicalData.Integers) : L.Carrier) - 1 = _
    rw [L.canonicalTopologicalData.filtrationIntegerUnit_coe]
  obtain ⟨z, hz, hex⟩ := hexpansion p F L hell htot m δ hd
  have hrem : n + 1 ≤ ((t + 1) * (Module.finrank F.Carrier L.Carrier - 1) + 2 * m) /
      Module.finrank F.Carrier L.Carrier :=
    hi.2.ge.trans (Nat.div_le_div_right (by change _ + (m + 1) ≤ _ + 2 * m; omega))
  obtain ⟨A, hA, hAt⟩ := trace_bound F L htot htrace hell t hpat m n hi.1.ge δ hd
  obtain ⟨C, hC, hCt⟩ := trace_bound F L htot htrace hell t hpat (2 * m) (n + 1) hrem z hz
  have hC0 := Ideal.pow_le_pow_right (Nat.le_succ n) hC
  have hB1 := Ideal.pow_le_pow_right hnm (integerNorm_mem_pow F L htot m δ hd)
  have hB := Ideal.pow_le_pow_right (Nat.le_succ n) hB1
  let qA := F.canonicalTopologicalData.idealQuotient πF hF n A hA
  let qB := F.canonicalTopologicalData.idealQuotient πF hF n (integerNorm F L δ) hB
  let qC := F.canonicalTopologicalData.idealQuotient πF hF n C hC0
  have hqB : F.canonicalTopologicalData.residue qB = 0 :=
    (F.canonicalTopologicalData.residue_idealQuotient_eq_zero_iff πF hF n (integerNorm F L δ) hB).mpr hB1
  have hqC : F.canonicalTopologicalData.residue qC = 0 :=
    (F.canonicalTopologicalData.residue_idealQuotient_eq_zero_iff πF hF n C hC0).mpr hC
  have hqAv : (qA : F.Carrier) = Algebra.trace F.Carrier L.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) / πF ^ n := by
    simp only [qA, idealQuotient_coe, hAt, hδ]
  have hqBv : (qB : F.Carrier) = Algebra.norm F.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) / πF ^ n := by
    simp only [qB, idealQuotient_coe, integerNorm_coe, hδ]
  have hqCv : (qC : F.Carrier) = Algebra.trace F.Carrier L.Carrier (z : L.Carrier) / πF ^ n := by
    simp only [qC, idealQuotient_coe, hCt]
  have he := coordinate_of_expansion F L πF hF m n x y hxy z qA qB qC hqAv hqBv hqCv
    (by simpa only [hδ, add_sub_cancel] using hex)
  rw [hqB, hqC, map_zero, add_zero, add_zero] at he
  rw [he]
  exact trace_term_coordinate F L htot πF hF πL hL m n
    (trace_bound F L htot htrace hell t hpat (m + 1) (n + 1) hi.2.ge) x b qA hb hqAv

end Langlands.LocalClassField.PrimeGradedNorm

namespace Langlands.LocalClassField
/-- All graded norm clauses follow from the two exact arithmetic propositions. -/
theorem primeGradedNormFromArithmetic.{u,v} : PrimeGradedNormFromArithmetic.{u,v} := by
  intro htrace hexpansion p _ F L _ _ _ _
  dsimp only
  intro hell htot t hpat
  obtain ⟨hfil, hnext⟩ := PrimeGradedNorm.filtration_containments_of_arithmetic F L htot
    htrace hexpansion hell t hpat
  refine ⟨PrimeGradedNorm.residue_bijective F L htot, hfil, hnext,
    PrimeGradedNorm.zero_coordinate F L htot, ?_⟩
  intro πF hF πL hL
  refine ⟨?_, ?_, ?_⟩
  · intro n hn hnt
    exact PrimeGradedNorm.below_break_of_arithmetic F L htot htrace hexpansion hell t hpat
      πF hF πL hL n hn hnt
  · intro ht
    exact PrimeGradedNorm.critical_of_arithmetic F L htot htrace hell t hpat hexpansion
      πF hF πL hL ht
  · intro n hnt
    exact PrimeGradedNorm.above_of_arithmetic F L htot htrace hell t hpat hexpansion
      πF hF πL hL n hnt
end Langlands.LocalClassField
