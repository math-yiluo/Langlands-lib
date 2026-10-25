import Langlands.ClassFieldTheory.Local.GradedNormCoordinateSupport
import Langlands.ClassFieldTheory.Local.PrimeNormTraceExpansionStatement
import Langlands.ClassFieldTheory.Local.PrimeRamifiedTraceIdealsStatement

/-! Integer-unit norm and elementary filtration transport. -/
noncomputable section
namespace Langlands.LocalClassField.PrimeGradedNorm
open Langlands.PadicField.TopologicalData
universe u v
variable {p : ℕ} [Fact p.Prime]
variable (F : PadicField.{u} p) (L : PadicField.{v} p)
variable [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
variable [FiniteDimensional F.Carrier L.Carrier]

/-- The actual norm restricted to integer rings, as a multiplicative map. -/
def integerNormHom : L.canonicalTopologicalData.Integers →* F.canonicalTopologicalData.Integers where
  toFun := integerNorm F L
  map_one' := by apply Subtype.ext; exact map_one (Algebra.norm F.Carrier)
  map_mul' := integerNorm_mul F L

/-- The actual norm on integer-ring units. -/
def integerUnitsNorm : L.canonicalTopologicalData.Integersˣ →* F.canonicalTopologicalData.Integersˣ :=
  Units.map (integerNormHom F L)

@[simp] theorem integerUnitsNorm_coe (x : L.canonicalTopologicalData.Integersˣ) :
    (integerUnitsNorm F L x : F.canonicalTopologicalData.Integers) =
      integerNorm F L (x : L.canonicalTopologicalData.Integers) := rfl

theorem integerUnitsNorm_inclusion (x : L.canonicalTopologicalData.Integersˣ) :
    F.canonicalTopologicalData.integerUnitsInclusion (integerUnitsNorm F L x) =
      normUnits F.Carrier L.Carrier (L.canonicalTopologicalData.integerUnitsInclusion x) := by
  apply Units.ext
  rfl

theorem norm_mem_filtration_iff (m n : ℕ) (x : L.canonicalTopologicalData.unitFiltration m) :
    normUnits F.Carrier L.Carrier (x : L.Carrierˣ) ∈ F.canonicalTopologicalData.unitFiltration n ↔
      integerNorm F L (L.canonicalTopologicalData.filtrationIntegerUnit m x : L.canonicalTopologicalData.Integers) - 1 ∈
        IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ n := by
  have hx : L.canonicalTopologicalData.integerUnitsInclusion
      (L.canonicalTopologicalData.filtrationIntegerUnit m x) = (x : L.Carrierˣ) := by
    apply Units.ext
    exact L.canonicalTopologicalData.filtrationIntegerUnit_coe m x
  rw [← hx, ← integerUnitsNorm_inclusion F L]
  rw [← integerUnitsNorm_coe]
  rw [← F.canonicalTopologicalData.mem_congruenceUnits_iff n]
  constructor
  · rintro ⟨y, hy, he⟩
    have h := F.canonicalTopologicalData.integerUnitsInclusion_injective he
    exact h ▸ hy
  · intro hy
    exact ⟨_, hy, rfl⟩

theorem norm_mem_filtration_zero (m : ℕ) (x : L.canonicalTopologicalData.unitFiltration m) :
    normUnits F.Carrier L.Carrier (x : L.Carrierˣ) ∈ F.canonicalTopologicalData.unitFiltration 0 := by
  simp [norm_mem_filtration_iff]

variable (htot : L.canonicalTopologicalData.ramificationIndex =
  Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex)
include htot

/-- Elementary filtration transport from an actual norm expansion and trace bounds. -/
theorem norm_mem_filtration_of_expansion
    (m n : ℕ) (hnm : n ≤ m) (x : L.canonicalTopologicalData.unitFiltration m)
    (z : L.canonicalTopologicalData.Integers)
    (a b : F.canonicalTopologicalData.Integers)
    (ha : a ∈ IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ n)
    (hb : b ∈ IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ n)
    (hat : (a : F.Carrier) = Algebra.trace F.Carrier L.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1))
    (hbt : (b : F.Carrier) = Algebra.trace F.Carrier L.Carrier (z : L.Carrier))
    (hex : Algebra.norm F.Carrier ((x : L.Carrierˣ) : L.Carrier) - 1 -
      Algebra.trace F.Carrier L.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) -
      Algebra.norm F.Carrier (((x : L.Carrierˣ) : L.Carrier) - 1) =
      Algebra.trace F.Carrier L.Carrier (z : L.Carrier)) :
    normUnits F.Carrier L.Carrier (x : L.Carrierˣ) ∈ F.canonicalTopologicalData.unitFiltration n := by
  let δ : L.canonicalTopologicalData.Integers :=
    (L.canonicalTopologicalData.filtrationIntegerUnit m x : L.canonicalTopologicalData.Integers) - 1
  have hd : δ ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ m :=
    (L.canonicalTopologicalData.mem_congruenceUnits_iff m _).mp
      (L.canonicalTopologicalData.filtrationIntegerUnit_mem m x)
  have hnd : integerNorm F L δ ∈ IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ n :=
    Ideal.pow_le_pow_right hnm (integerNorm_mem_pow F L htot m δ hd)
  rw [norm_mem_filtration_iff]
  have he : integerNorm F L
      (L.canonicalTopologicalData.filtrationIntegerUnit m x : L.canonicalTopologicalData.Integers) - 1 =
      a + integerNorm F L δ + b := by
    apply Subtype.ext
    change Algebra.norm F.Carrier
      ((L.canonicalTopologicalData.filtrationIntegerUnit m x : L.canonicalTopologicalData.Integers) : L.Carrier) - 1 =
      (a : F.Carrier) + Algebra.norm F.Carrier (δ : L.Carrier) + (b : F.Carrier)
    change _ = (a : F.Carrier) + Algebra.norm F.Carrier
      (((L.canonicalTopologicalData.filtrationIntegerUnit m x : L.canonicalTopologicalData.Integers) : L.Carrier) - 1) + (b : F.Carrier)
    rw [L.canonicalTopologicalData.filtrationIntegerUnit_coe, hat, hbt]
    linear_combination hex
  rw [he]
  exact Ideal.add_mem _ (Ideal.add_mem _ ha hnd) hb

variable [IsGalois F.Carrier L.Carrier]

/-- A conditional assembly step; the two arithmetic propositions are explicit inputs. -/
theorem norm_mem_filtration_of_arithmetic
    (htrace : PrimeRamifiedTraceIdeals.{u,v}) (hexpansion : PrimeNormTraceExpansion.{u,v})
    (hell : Nat.Prime (Module.finrank F.Carrier L.Carrier)) (t : ℕ)
    (hpat : ∀ i : ℕ, Ramification.Padic.lowerRamificationGroup L.canonicalTopologicalData F.Carrier i =
      if i ≤ t then ⊤ else ⊥)
    (m n : ℕ) (hnm : n ≤ m)
    (hbound : n ≤ ((t + 1) * (Module.finrank F.Carrier L.Carrier - 1) + m) /
      Module.finrank F.Carrier L.Carrier)
    (x : L.canonicalTopologicalData.unitFiltration m) :
    normUnits F.Carrier L.Carrier (x : L.Carrierˣ) ∈ F.canonicalTopologicalData.unitFiltration n := by
  let δ : L.canonicalTopologicalData.Integers :=
    (L.canonicalTopologicalData.filtrationIntegerUnit m x : L.canonicalTopologicalData.Integers) - 1
  have hd : δ ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ m :=
    (L.canonicalTopologicalData.mem_congruenceUnits_iff m _).mp
      (L.canonicalTopologicalData.filtrationIntegerUnit_mem m x)
  have hδ : (δ : L.Carrier) = ((x : L.Carrierˣ) : L.Carrier) - 1 := by
    change ((L.canonicalTopologicalData.filtrationIntegerUnit m x : L.canonicalTopologicalData.Integers) : L.Carrier) - 1 = _
    rw [L.canonicalTopologicalData.filtrationIntegerUnit_coe]
  obtain ⟨z, hz, he⟩ := hexpansion p F L hell htot m δ hd
  obtain ⟨a, ha, hat⟩ := (htrace p F L hell htot t hpat m
    (Algebra.trace F.Carrier L.Carrier (δ : L.Carrier))).mp ⟨δ, hd, rfl⟩
  obtain ⟨b, hb, hbt⟩ := (htrace p F L hell htot t hpat (2 * m)
    (Algebra.trace F.Carrier L.Carrier (z : L.Carrier))).mp ⟨z, hz, rfl⟩
  apply norm_mem_filtration_of_expansion F L htot m n hnm x z a b
  · exact Ideal.pow_le_pow_right hbound ha
  · apply Ideal.pow_le_pow_right (hbound.trans ?_) hb
    exact Nat.div_le_div_right (by omega)
  · simpa only [hδ] using hat
  · exact hbt
  · simpa only [hδ, add_sub_cancel] using he

omit htot in
theorem graded_index_bounds (ell t n : ℕ) (hell : 0 < ell) :
    let m := if n ≤ t then n else t + ell * (n - t)
    n ≤ m ∧
      n ≤ ((t + 1) * (ell - 1) + m) / ell ∧
      n + 1 ≤ ((t + 1) * (ell - 1) + (m + 1)) / ell := by
  have he : ell - 1 + 1 = ell := by omega
  split_ifs with h
  · refine ⟨le_rfl, (Nat.le_div_iff_mul_le hell).mpr ?_, (Nat.le_div_iff_mul_le hell).mpr ?_⟩
    · have := Nat.mul_le_mul_right (ell - 1) (show n ≤ t + 1 by omega)
      nlinarith
    · have := Nat.mul_le_mul_right (ell - 1) (show n + 1 ≤ t + 1 by omega)
      nlinarith
  · have hn : t + (n - t) = n := by omega
    refine ⟨?_, (Nat.le_div_iff_mul_le hell).mpr ?_, (Nat.le_div_iff_mul_le hell).mpr ?_⟩ <;>
      nlinarith [Nat.mul_le_mul_right (n - t) (show 1 ≤ ell by omega)]

/-- Both norm containments, conditional on the genuine arithmetic inputs. -/
theorem filtration_containments_of_arithmetic
    (htrace : PrimeRamifiedTraceIdeals.{u,v}) (hexpansion : PrimeNormTraceExpansion.{u,v})
    (hell : Nat.Prime (Module.finrank F.Carrier L.Carrier)) (t : ℕ)
    (hpat : ∀ i : ℕ, Ramification.Padic.lowerRamificationGroup L.canonicalTopologicalData F.Carrier i =
      if i ≤ t then ⊤ else ⊥) :
    let ψ := fun n => if n ≤ t then n else t + Module.finrank F.Carrier L.Carrier * (n - t)
    (∀ (n : ℕ) (x : L.canonicalTopologicalData.unitFiltration (ψ n)),
      normUnits F.Carrier L.Carrier (x : L.Carrierˣ) ∈ F.canonicalTopologicalData.unitFiltration n) ∧
    (∀ (n : ℕ) (x : L.canonicalTopologicalData.unitFiltration (ψ n + 1)),
      normUnits F.Carrier L.Carrier (x : L.Carrierˣ) ∈ F.canonicalTopologicalData.unitFiltration (n + 1)) := by
  dsimp only
  constructor
  · intro n x
    have hh := graded_index_bounds (Module.finrank F.Carrier L.Carrier) t n hell.pos
    exact norm_mem_filtration_of_arithmetic F L htot htrace hexpansion hell t hpat _ n hh.1 hh.2.1 x
  · intro n x
    have hh := graded_index_bounds (Module.finrank F.Carrier L.Carrier) t n hell.pos
    exact norm_mem_filtration_of_arithmetic F L htot htrace hexpansion hell t hpat _ (n + 1)
      (Nat.add_le_add_right hh.1 1) hh.2.2 x

end Langlands.LocalClassField.PrimeGradedNorm
