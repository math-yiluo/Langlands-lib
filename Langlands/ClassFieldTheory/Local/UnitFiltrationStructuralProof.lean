import Langlands.ClassFieldTheory.Local.UnitFiltrationTopologyStatement
import Langlands.LocalField.Topology
import Mathlib.RingTheory.Filtration

/-! Structural laws for the actual reduction-kernel unit filtration. -/

namespace Langlands.PadicField.TopologicalData

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- Reduction-kernel membership is congruence to one in the integer ring. -/
theorem mem_congruenceUnits_iff (n : ℕ) (x : T.Integersˣ) :
    x ∈ T.congruenceUnits n ↔
      (x : T.Integers) - 1 ∈ (IsLocalRing.maximalIdeal T.Integers) ^ n := by
  change T.truncatedUnitsReduction n x = 1 ↔ _
  rw [← Units.val_inj]
  exact Ideal.Quotient.mk_eq_one_iff_sub_mem _

/-- The integer-unit inclusion is injective. -/
theorem integerUnitsInclusion_injective : Function.Injective T.integerUnitsInclusion :=
  Units.map_injective Subtype.val_injective

/-- Powers of the maximal ideal give a decreasing reduction kernel. -/
theorem congruenceUnits_antitone : Antitone T.congruenceUnits := by
  intro m n h x hx
  exact (T.mem_congruenceUnits_iff m x).mpr
    (Ideal.pow_le_pow_right h ((T.mem_congruenceUnits_iff n x).mp hx))

/-- The actual field-unit filtration is decreasing. -/
theorem unitFiltration_antitone : Antitone T.unitFiltration := by
  intro m n h
  exact Subgroup.map_mono (T.congruenceUnits_antitone h)

/-- At level zero the integer-unit reduction kernel is the full group. -/
theorem congruenceUnits_zero : T.congruenceUnits 0 = ⊤ := by
  ext x
  simp [T.mem_congruenceUnits_iff]

/-- The zeroth filtration group is exactly the valuation-unit subgroup. -/
theorem unitFiltration_zero : T.unitFiltration 0 = T.unitSubgroup := by
  ext x
  constructor
  · rintro ⟨y, _, rfl⟩
    exact (T.integerUnitsEquiv.symm y).property
  · intro hx
    refine ⟨T.integerUnitsEquiv ⟨x, hx⟩, ?_, ?_⟩
    · rw [T.congruenceUnits_zero]
      trivial
    · apply Units.ext
      rfl

/-- Every reduction kernel is closed in the actual integer-unit topology. -/
theorem isClosed_congruenceUnits (n : ℕ) :
    let := T.topology
    IsClosed (T.congruenceUnits n : Set T.Integersˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  have h := IsNoetherianRing.isClosed_ideal
    ((IsLocalRing.maximalIdeal T.Integers) ^ n)
  have he : (T.congruenceUnits n : Set T.Integersˣ) =
      (fun x : T.Integersˣ => (x : T.Integers) - 1) ⁻¹'
        (((IsLocalRing.maximalIdeal T.Integers) ^ n : Ideal T.Integers) : Set T.Integers) := by
    ext x
    exact T.mem_congruenceUnits_iff n x
  rw [he]
  exact h.preimage (Units.continuous_val.sub continuous_const)

/-- All levels, including zero, are compact in the field-unit topology. -/
theorem isCompact_unitFiltration (n : ℕ) :
    let := T.topology
    IsCompact (T.unitFiltration n : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  exact (T.isClosed_congruenceUnits n).isCompact.image
    T.integerUnitsInclusionContinuous.continuous

/-- All levels are closed in the Hausdorff field-unit topology. -/
theorem isClosed_unitFiltration (n : ℕ) :
    let := T.topology
    IsClosed (T.unitFiltration n : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  exact (T.isCompact_unitFiltration n).isClosed

/-- Krull intersection separates the integer-unit congruence kernels. -/
theorem congruenceUnits_separated (x : T.Integersˣ)
    (hx : ∀ n : ℕ, x ∈ T.congruenceUnits n) : x = 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  have h : (x : T.Integers) - 1 ∈
      ⨅ n : ℕ, (IsLocalRing.maximalIdeal T.Integers) ^ n := by
    exact (Submodule.mem_iInf _).mpr (fun n => (T.mem_congruenceUnits_iff n x).mp (hx n))
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'] at h
  exact Units.ext (sub_eq_zero.mp h)

/-- A field unit in every actual filtration level is one. -/
theorem unitFiltration_separated (x : F.Carrierˣ)
    (hx : ∀ n : ℕ, x ∈ T.unitFiltration n) : x = 1 := by
  obtain ⟨y, _, hy⟩ := hx 0
  have hyall : ∀ n, y ∈ T.congruenceUnits n := by
    intro n
    obtain ⟨z, hz, he⟩ := hx n
    have hz' : z = y := T.integerUnitsInclusion_injective (he.trans hy.symm)
    simpa [hz'] using hz
  rw [← hy, T.congruenceUnits_separated y hyall, map_one]

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalClassField

universe u

/-- Structural topology laws for all supplied local-field realizations. -/
theorem unitFiltrationStructuralLaws : UnitFiltrationStructuralLaws.{u} := by
  intro p hp F T
  exact ⟨fun n => ⟨T.isCompact_unitFiltration n, T.isClosed_unitFiltration n⟩,
    T.unitFiltration_antitone, T.unitFiltration_separated, T.unitFiltration_zero⟩

end Langlands.LocalClassField
