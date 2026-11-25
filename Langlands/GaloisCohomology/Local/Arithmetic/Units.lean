import Langlands.ClassFieldTheory.Global.LocalUnitPowers
import Langlands.GaloisCohomology.Local.Arithmetic.Powers
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
import Mathlib.RingTheory.LocalRing.Quotient

/-!
# The unit filtration of a nonarchimedean local field

Elementary facts about the units of the ring of integers `𝒪[K]` of a nonarchimedean local field:
the unit filtration `U^n = 1 + 𝓂^n` (the NYLL copy's `LocalFieldTheory.principalUnits`), the
description of `𝓂^n` by a uniformizer, units of valuation one, and the extraction of roots of
principal units (Hensel's lemma, from the Library's `exists_isRoot_of_isAdicComplete`).
-/

noncomputable section

namespace Langlands.GaloisCohomology.Local

open ValuativeRel IsLocalRing Polynomial ClassFieldTheory.Local

universe u

section Filtration

variable (K : Type u) [Field K] [ValuativeRel K]

/-- The unit filtration `U^n = {u ∈ 𝒪[K]ˣ | u − 1 ∈ 𝓂^n}`: the NYLL copy's principal units. -/
abbrev unitFiltration (n : ℕ) : Subgroup 𝒪[K]ˣ :=
  LocalFieldTheory.principalUnits K n

variable {K} in
theorem mem_unitFiltration {n : ℕ} {u : 𝒪[K]ˣ} :
    u ∈ unitFiltration K n ↔ (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ n :=
  LocalFieldTheory.mem_principalUnits_iff K u n

theorem unitFiltration_zero : unitFiltration K 0 = ⊤ :=
  LocalFieldTheory.principalUnits_zero K

theorem unitFiltration_antitone : Antitone (unitFiltration K) :=
  fun _ _ hmn => LocalFieldTheory.principalUnits_antitone K hmn

/-- Reduction of units to the residue field. -/
def unitsToResidue : 𝒪[K]ˣ →* 𝓀[K]ˣ :=
  Units.map (residue 𝒪[K]).toMonoidHom

variable {K} in
theorem coe_unitsToResidue (u : 𝒪[K]ˣ) :
    ((unitsToResidue K u : 𝓀[K]ˣ) : 𝓀[K]) = residue 𝒪[K] (u : 𝒪[K]) := rfl

theorem ker_unitsToResidue : (unitsToResidue K).ker = unitFiltration K 1 := by
  ext u
  rw [MonoidHom.mem_ker, mem_unitFiltration, pow_one, ← residue_eq_zero_iff, map_sub, map_one,
    sub_eq_zero, Units.ext_iff, coe_unitsToResidue, Units.val_one]

end Filtration

section Uniformizer

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem mem_maximalIdeal_pow_iff {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n : ℕ} {x : 𝒪[K]} :
    x ∈ 𝓂[K] ^ n ↔ ϖ ^ n ∣ x := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem mem_maximalIdeal_iff_dvd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {x : 𝒪[K]} :
    x ∈ 𝓂[K] ↔ ϖ ∣ x := by
  simpa using mem_maximalIdeal_pow_iff hϖ (n := 1) (x := x)

theorem uniformizer_mem_maximalIdeal {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) : ϖ ∈ 𝓂[K] :=
  (mem_maximalIdeal_iff_dvd hϖ).mpr dvd_rfl

theorem exists_sub_one_eq_mul {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n : ℕ} (u : unitFiltration K n) :
    ∃ a : 𝒪[K], ((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ϖ ^ n * a :=
  (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp u.2)

/-- The unit filtration has finite index: `U^n` is the kernel of `𝒪[K]ˣ → (𝒪[K]/𝓂^n)ˣ`. -/
instance unitFiltration_finiteIndex (n : ℕ) : (unitFiltration K n).FiniteIndex := by
  have : Finite (𝒪[K] ⧸ 𝓂[K] ^ n) := IsLocalRing.finite_quotient_iff.mpr ⟨n, le_rfl⟩
  have h : unitFiltration K n = integerCongruenceUnits K (𝓂[K] ^ n) := by
    ext u
    rw [mem_unitFiltration, mem_integerCongruenceUnits_iff]
  rw [h]
  exact Subgroup.finiteIndex_ker _

end Uniformizer

section Units

variable {K : Type u} [Field K] [ValuativeRel K]

theorem valuation_unit (u : 𝒪[K]ˣ) : valuation K ((u : 𝒪[K]) : K) = 1 :=
  (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp u.isUnit

theorem valuation_lt_one_of_mem_maximalIdeal {x : 𝒪[K]} (hx : x ∈ 𝓂[K]) :
    valuation K (x : K) < 1 := by
  refine lt_of_le_of_ne x.2 fun h ↦ ?_
  exact (IsLocalRing.mem_maximalIdeal x).mp hx
    ((Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mpr h)

theorem isUnit_unit_add {η : 𝒪[K]ˣ} {x : 𝒪[K]} (hx : x ∈ 𝓂[K]) : IsUnit ((η : 𝒪[K]) + x) := by
  have h1 : IsUnit (1 + (η⁻¹ : 𝒪[K]ˣ) * x) := by
    simpa using isUnit_one_sub_self_of_mem_nonunits (-(((η⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * x))
      ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem (Ideal.mul_mem_left _ _ hx)))
  have : (η : 𝒪[K]) + x = η * (1 + (η⁻¹ : 𝒪[K]ˣ) * x) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  rw [this]
  exact η.isUnit.mul h1

/-- A unit of `K` lies in `𝒪[K]ˣ` exactly when its valuation is one. -/
theorem mem_range_integerUnitsMap_iff {x : Kˣ} :
    x ∈ (integerUnitsMap K).range ↔ valuation K (x : K) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact valuation_unit u
  · intro h
    exact ⟨integerUnitOfValuationEqOne x h, Units.ext rfl⟩

end Units

section Roots

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- For `m` invertible in the residue field, every principal unit is the `m`-th power of a
principal unit (Hensel's lemma for a simple root). -/
theorem exists_pow_eq_of_mem_unitFiltration_one {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) {w : 𝒪[K]ˣ}
    (hw : w ∈ unitFiltration K 1) : ∃ u ∈ unitFiltration K 1, u ^ m = w := by
  have hu : IsUnit (m : 𝒪[K]) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]; exact hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have := isAdicComplete_integer K
  set f : 𝒪[K][X] := X ^ m - C (w : 𝒪[K])
  have h₁ : f.eval 1 ∈ 𝓂[K] := by
    have hw' : (w : 𝒪[K]) - 1 ∈ 𝓂[K] := by simpa using mem_unitFiltration.mp hw
    have e' : f.eval 1 = -((w : 𝒪[K]) - 1) := by simp [f]
    rw [e']
    exact neg_mem hw'
  have h₂ : IsUnit (Ideal.Quotient.mk 𝓂[K] (f.derivative.eval 1)) := by
    have : f.derivative.eval 1 = (m : 𝒪[K]) := by simp [f, derivative_X_pow]
    rw [this]
    exact hu.map _
  obtain ⟨b, hb, hb1⟩ := ClassFieldTheory.Global.exists_isRoot_of_isAdicComplete 𝓂[K] f 1 h₁ h₂
  have hbm : b ^ m = w := by simpa [f, sub_eq_zero] using hb.eq_zero
  have hbu : IsUnit b := (isUnit_pow_iff hm0).mp (hbm ▸ w.isUnit)
  refine ⟨hbu.unit, ?_, by ext; simp [hbm]⟩
  rw [mem_unitFiltration, pow_one]
  simpa using hb1

/-- For a prime `p = ϖ^e ε` and `k ≥ e + 1`, every unit of `U^{k+e}` is the `p`-th power of a unit
of `U^k` (Hensel's lemma for `p`-th powers, the Library's `exists_one_add_mul_mul_pow_eq`). -/
theorem exists_pow_eq_of_mem_unitFiltration {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {p : ℕ}
    (hp : p.Prime) {e : ℕ} {ε : 𝒪[K]ˣ} (hpe : (p : 𝒪[K]) = ϖ ^ e * ε) {k : ℕ} (hk : e + 1 ≤ k)
    {w : 𝒪[K]ˣ} (hw : w ∈ unitFiltration K (k + e)) : ∃ u ∈ unitFiltration K k, u ^ p = w := by
  obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ ⟨w, hw⟩
  have := isAdicComplete_integer K
  set c : 𝒪[K] := ϖ ^ (k - e)
  have hc : c ∈ 𝓂[K] :=
    Ideal.pow_mem_of_mem _ (uniformizer_mem_maximalIdeal hϖ) _ (by omega)
  set t : 𝒪[K] := ((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ 2 * a
  obtain ⟨z, hz⟩ := ClassFieldTheory.Global.exists_one_add_mul_mul_pow_eq 𝓂[K] p hp.ne_zero c hc t
  have hwt : (w : 𝒪[K]) = 1 + (p : 𝒪[K]) ^ 2 * c * t := by
    have hke : k + e = 2 * e + (k - e) := by omega
    have : (w : 𝒪[K]) = 1 + ϖ ^ (k + e) * a := by simp only at ha; rw [← ha]; ring
    rw [this, hpe, hke, pow_add, pow_mul]
    simp only [c, t, mul_pow]
    have hεε : (ε : 𝒪[K]) * ((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) = 1 := Units.mul_inv ε
    linear_combination (-(ϖ ^ e) ^ 2 * ϖ ^ (k - e) * a *
      (1 + (ε : 𝒪[K]) * ((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]))) * hεε
  have hbu : IsUnit (1 + (p : 𝒪[K]) * c * z) :=
    (isUnit_pow_iff hp.ne_zero).mp (by rw [hz, ← hwt]; exact w.isUnit)
  refine ⟨hbu.unit, ?_, Units.ext (by simp [hz, hwt])⟩
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ]
  refine ⟨ε * z, ?_⟩
  simp only [IsUnit.unit_spec, add_sub_cancel_left, c, hpe]
  rw [show k = e + (k - e) by omega, pow_add]
  simp only [show e + (k - e) - e = k - e by omega]
  ring

end Roots

end Langlands.GaloisCohomology.Local
