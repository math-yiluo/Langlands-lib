import Langlands.AllFieldBZ.LocalField.Definitions
import Langlands.HarmonicAnalysis.Conductor

/-!
# All-field port of `Langlands.HarmonicAnalysis.Conductor`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.HarmonicAnalysis.Conductor` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped WithZero
open Topology
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe u
variable {F : LocalFieldPackage.{u}} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology

/-- The discrete valuation has exactly the already specified integer ring. -/
theorem mem_integers_iff_discreteValuation_le_one (x : F.Carrier) :
    x ∈ T.Integers ↔ T.discreteValuation x ≤ 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  change ValuativeRel.valuation F.Carrier x ≤ 1 ↔
    e (ValuativeRel.valuation F.Carrier x) ≤ 1
  rw [← map_one e]
  exact e.strictMono.le_iff_le.symm

private theorem conductor_uniformizer_value :
    T.discreteValuation T.uniformizer = WithZero.exp (-1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have h : ValuativeRel.valuation F.Carrier T.uniformizer =
      e.symm (WithZero.exp (-1)) :=
    (ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1)))).choose_spec
  change e (ValuativeRel.valuation F.Carrier T.uniformizer) = WithZero.exp (-1)
  rw [h, e.apply_symm_apply]

/-- The additive lattice of elements of order at least `-n`.
This is the fractional ideal convention `π^(-n) O`, so it increases with `n`. -/
def additiveLattice (n : ℤ) : AddSubgroup F.Carrier where
  carrier := {x | T.discreteValuation x ≤ WithZero.exp n}
  zero_mem' := by simp
  add_mem' hx hy := (T.discreteValuation.map_add _ _).trans (max_le hx hy)
  neg_mem' hx := by simpa using hx

@[simp]
theorem mem_additiveLattice (n : ℤ) (x : F.Carrier) :
    x ∈ T.additiveLattice n ↔ T.discreteValuation x ≤ WithZero.exp n := Iff.rfl

theorem additiveLattice_mono : Monotone T.additiveLattice := by
  intro m n h x hx
  exact hx.trans (WithZero.exp_le_exp.mpr h)

/-- The valuation-lattice definition is precisely the fractional ideal
`π^(-n) O`, using the actual chosen uniformizer and integer ring. -/
theorem mem_additiveLattice_iff_div_mem_integers (n : ℤ) (x : F.Carrier) :
    x ∈ T.additiveLattice n ↔ x / T.uniformizer ^ (-n) ∈ T.Integers := by
  rw [mem_additiveLattice, T.mem_integers_iff_discreteValuation_le_one]
  have hv : T.discreteValuation (T.uniformizer ^ (-n)) = WithZero.exp n := by
    rw [map_zpow₀, T.conductor_uniformizer_value, ← WithZero.exp_zsmul]
    congr 1
    simp
  rw [T.discreteValuation.map_div, hv]
  exact (div_le_one₀ WithZero.exp_pos).symm

/-- At level zero the additive lattice is the actual integer ring. -/
theorem mem_additiveLattice_zero (x : F.Carrier) :
    x ∈ T.additiveLattice 0 ↔ x ∈ T.Integers := by
  simp [T.mem_additiveLattice_iff_div_mem_integers]

/-- Every neighborhood of zero contains an actual valuation lattice. -/
theorem exists_additiveLattice_subset {s : Set F.Carrier}
    (hs : s ∈ @nhds F.Carrier T.topology 0) :
    ∃ n : ℤ, (T.additiveLattice n : Set F.Carrier) ⊆ s := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨γ, hγ, hγs⟩ :=
    (IsValuativeTopology.hasBasis_nhds_zero' F.Carrier).mem_iff.mp hs
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have heγ : e γ ≠ 0 := by simpa using hγ
  refine ⟨WithZero.log (e γ) - 1, fun x hx => hγs ?_⟩
  change ValuativeRel.valuation F.Carrier x < γ
  apply e.strictMono.lt_iff_lt.mp
  calc
    e (ValuativeRel.valuation F.Carrier x) ≤
        WithZero.exp (WithZero.log (e γ) - 1) := hx
    _ < WithZero.exp (WithZero.log (e γ)) :=
      WithZero.exp_lt_exp.mpr (by omega)
    _ = e γ := WithZero.exp_log heγ

open Langlands.HarmonicAnalysis
/-- The character is trivial on the full fractional ideal `π^(-n) O`. -/
def AdditiveTrivialAt (ψ : AdditiveCharacter) (n : ℤ) : Prop :=
  ∀ x ∈ T.additiveLattice n, ψ x = 1

/-- Continuity gives a lattice on which the additive character is trivial.
The proof uses the fact that the right half-circle contains no nontrivial subgroup. -/
theorem exists_additiveTrivialAt (ψ : AdditiveCharacter) :
    ∃ n : ℤ, T.AdditiveTrivialAt ψ n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let s := ψ ⁻¹' Circle.centeredArc (Real.pi / 2)
  have hs : s ∈ 𝓝 (0 : F.Carrier) := by
    apply (Circle.isOpen_centeredArc _).preimage ψ.continuous_toFun |>.mem_nhds
    change ψ.toAddChar 0 ∈ Circle.centeredArc (Real.pi / 2)
    rw [AddChar.map_zero_eq_one]
    exact ⟨0, by simpa using (half_pos Real.pi_pos), Circle.exp_zero⟩
  obtain ⟨n, hn⟩ := T.exists_additiveLattice_subset hs
  refine ⟨n, fun x hx => ?_⟩
  apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
  intro k _hk
  rw [← AddChar.map_nsmul_eq_pow]
  exact hn ((T.additiveLattice n).nsmul_mem hx k)

/-- Nontriviality supplies an upper bound for all triviality levels. -/
theorem additiveTrivialAt_bddAbove (ψ : AdditiveCharacter) :
    ∃ b : ℤ, ∀ n : ℤ, T.AdditiveTrivialAt ψ n → n ≤ b := by
  let := T.topology
  obtain ⟨x, hx⟩ : ∃ x : F.Carrier, ψ x ≠ 1 := by
    by_contra h
    push Not at h
    exact ψ.nontrivial (AddChar.ext _ _ h)
  refine ⟨WithZero.log (T.discreteValuation x), fun n hn => ?_⟩
  apply le_of_not_gt
  intro h
  exact hx (hn x (WithZero.le_exp_of_log_le h.le))

/-- The largest integer triviality level exists; it is not assumed as character data. -/
theorem exists_additiveConductor (ψ : AdditiveCharacter) :
    ∃ n : ℤ, T.AdditiveTrivialAt ψ n ∧
      ∀ m : ℤ, T.AdditiveTrivialAt ψ m → m ≤ n :=
  Int.exists_greatest_of_bdd (T.additiveTrivialAt_bddAbove ψ)
    (T.exists_additiveTrivialAt ψ)

/-- Tate's integer `n(ψ)`, the largest `n` for which `ψ(π^(-n) O)=1`.
Choice is made only from the proved existence theorem immediately above. -/
def additiveConductor (ψ : AdditiveCharacter) : ℤ :=
  (T.exists_additiveConductor ψ).choose

theorem additiveConductor_spec (ψ : AdditiveCharacter) :
    T.AdditiveTrivialAt ψ (T.additiveConductor ψ) ∧
      ∀ m : ℤ, T.AdditiveTrivialAt ψ m → m ≤ T.additiveConductor ψ :=
  (T.exists_additiveConductor ψ).choose_spec

/-- The unit filtration, including `U⁰ = Oˣ`. For positive `n` the second
condition is the usual congruence to one modulo the `n`th maximal-ideal power. -/
def principalUnits (n : ℕ) : Subgroup F.Carrierˣ where
  carrier := {u | T.discreteValuation (u : F.Carrier) = 1 ∧
    T.discreteValuation ((u : F.Carrier) - 1) ≤ WithZero.exp (-(n : ℤ))}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    constructor
    · simpa using congrArg₂ (· * ·) hu.1 hv.1
    · change T.discreteValuation ((u : F.Carrier) * v - 1) ≤ _
      rw [show (u : F.Carrier) * v - 1 =
        u * ((v : F.Carrier) - 1) + ((u : F.Carrier) - 1) by ring]
      apply T.discreteValuation.map_add_le _ hu.2
      simpa [map_mul, hu.1] using hv.2
  inv_mem' := by
    intro u hu
    constructor
    · simpa using congrArg Inv.inv hu.1
    · simp only [Units.val_inv_eq_inv_val]
      rw [show (u : F.Carrier)⁻¹ - 1 =
        -((u : F.Carrier) - 1) * (u : F.Carrier)⁻¹ by
          field_simp
          ring]
      simpa only [map_mul, Valuation.map_neg, map_inv₀, hu.1, inv_one, mul_one] using hu.2

@[simp]
theorem mem_principalUnits (n : ℕ) (u : F.Carrierˣ) :
    u ∈ T.principalUnits n ↔ T.discreteValuation (u : F.Carrier) = 1 ∧
      T.discreteValuation ((u : F.Carrier) - 1) ≤ WithZero.exp (-(n : ℤ)) := Iff.rfl

@[simp]
theorem mem_principalUnits_zero (u : F.Carrierˣ) :
    u ∈ T.principalUnits 0 ↔ T.discreteValuation (u : F.Carrier) = 1 := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    simpa using T.discreteValuation.map_sub_le h.le (by simp : T.discreteValuation 1 ≤ 1)

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
