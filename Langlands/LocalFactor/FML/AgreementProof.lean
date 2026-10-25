import Langlands.LocalFactor.FML.AgreementStatement

/-!
# FML and Library conductor agreement proofs

Derived integration proofs by Worker 96 for the statements of Worker 40,
using Worker 20's adaptation of Fukuhiro Ueda's epsilon_FML, commit
0b4159be50e1bd45ddff1de4280399576a3e2024 (Apache-2.0).
The imported definitions and their attribution/license notices are unchanged.
See AgreementProof.md for the implemented proof route and source correspondence.
-/

namespace Langlands.FML.Padic

universe u
open scoped WithZero

section Comparisons

variable {p : ℕ} [Fact p.Prime] {F : Langlands.PadicField.{u} p}
  (T : F.TopologicalData)

/-- The lattice comparison includes zero, whose FML additive order is infinity. -/
theorem mem_lattice_iff_mem_additiveLattice (n : ℤ) (x : F.Carrier) :
    x ∈ lattice T (-n) ↔ x ∈ T.additiveLattice n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  change ((-n : ℤ) : WithTop ℤ) ≤
    (if normalizedValuation T x = 0 then ⊤ else
      ((-WithZero.log (normalizedValuation T x) : ℤ) : WithTop ℤ)) ↔
    T.discreteValuation x ≤ WithZero.exp n
  rw [normalizedValuation_eq_discreteValuation]
  by_cases hx : x = 0
  · simp [hx]
  · have hv := T.discreteValuation.ne_zero_iff.mpr hx
    simp only [ite_eq_right hv, WithTop.coe_le_coe, neg_le_neg_iff]
    exact WithZero.log_le_iff_le_exp hv

/-- Integral-unit membership is preserved by the same normalized valuation map. -/
theorem mem_unitGroup_iff_discreteValuation_eq_one (x : F.Carrierˣ) :
    letI := T.valuativeRel
    x ∈ FML.unitGroup F.Carrier ↔ T.discreteValuation (x : F.Carrier) = 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [Valuation.mem_unitGroup_iff]
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  change ValuativeRel.valuation F.Carrier (x : F.Carrier) = 1 ↔
    e (ValuativeRel.valuation F.Carrier (x : F.Carrier)) = 1
  rw [← map_one e]
  exact e.injective.eq_iff.symm

end Comparisons

/-- Exact proof of the published universally quantified lattice target. -/
theorem latticeAgreement : LatticeAgreementStatement.{u} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro n
  ext x
  exact mem_lattice_iff_mem_additiveLattice T n x

/-- Exact proof of the published unit-filtration target, including level zero. -/
theorem unitFiltrationAgreement : UnitFiltrationAgreementStatement.{u} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro k
  ext x
  cases k with
  | zero =>
      rw [FML.unitFiltration_zero, T.mem_principalUnits_zero]
      exact mem_unitGroup_iff_discreteValuation_eq_one T x
  | succ k =>
      rw [FML.mem_unitFiltration_succ, T.mem_principalUnits,
        mem_unitGroup_iff_discreteValuation_eq_one T]
      apply and_congr_right
      intro _
      simpa only [neg_neg, Padic.lattice, T.mem_additiveLattice] using
        mem_lattice_iff_mem_additiveLattice T (-((k + 1 : ℕ) : ℤ))
          ((x : F.Carrier) - 1)

section Triviality

variable {p : ℕ} [Fact p.Prime] {F : Langlands.PadicField.{u} p}
  (T : F.TopologicalData)

/-- Whole-lattice triviality is unchanged by the injective circle-to-units map. -/
theorem addCharTrivialOnLattice_iff
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℤ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    FML.AddCharTrivialOnLattice F.Carrier (FML.ofUnitaryAdditiveCharacter ψ) (-n) ↔
      T.AdditiveTrivialAt ψ n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hvalue (x : F.Carrier) :
      FML.ofUnitaryAdditiveCharacter ψ x = 1 ↔ ψ x = 1 := by
    rw [FML.ofUnitaryAdditiveCharacter_apply, ← map_one Circle.toUnits]
    exact FML.circle_toUnits_injective.eq_iff
  simp only [FML.AddCharTrivialOnLattice,
    Langlands.PadicField.TopologicalData.AdditiveTrivialAt, hvalue]
  apply forall_congr'
  intro x
  rw [show x ∈ FML.lattice F.Carrier (-n) ↔ x ∈ T.additiveLattice n from
    mem_lattice_iff_mem_additiveLattice T n x]

/-- Whole-subgroup triviality uses the same continuous quasicharacter. -/
theorem quasiCharTrivialOnUnitFiltration_iff
    (χ : @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology) (m : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    FML.QuasiCharTrivialOnUnitFiltration F.Carrier χ m ↔
      T.MultiplicativeTrivialAt χ m := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  unfold FML.QuasiCharTrivialOnUnitFiltration
    Langlands.PadicField.TopologicalData.MultiplicativeTrivialAt
  rw [unitFiltrationAgreement F T m]

end Triviality

/-- Exact proof of the published additive-conductor target. -/
theorem additiveConductorAgreement : AdditiveConductorAgreementStatement.{u} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ n
  constructor
  · intro h
    have hn : n ≤ T.additiveConductor ψ :=
      (T.additiveTrivialAt_iff_le_conductor ψ n).mp
        ((addCharTrivialOnLattice_iff T ψ n).mp h.1)
    have hc : -n ≤ -T.additiveConductor ψ :=
      h.2 _ ((addCharTrivialOnLattice_iff T ψ _).mpr (T.additiveConductor_spec ψ).1)
    omega
  · rintro rfl
    refine ⟨(addCharTrivialOnLattice_iff T ψ _).mpr
      (T.additiveConductor_spec ψ).1, ?_⟩
    intro r hr
    have hr' : T.AdditiveTrivialAt ψ (-r) :=
      (addCharTrivialOnLattice_iff T ψ (-r)).mp (by simpa only [neg_neg] using hr)
    have hle := (T.additiveTrivialAt_iff_le_conductor ψ (-r)).mp hr'
    omega

/-- Exact proof of the published multiplicative-conductor target. -/
theorem multiplicativeConductorAgreement :
    MultiplicativeConductorAgreementStatement.{u} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro χ m
  constructor
  · intro h
    apply le_antisymm
    · exact h.2 _ ((quasiCharTrivialOnUnitFiltration_iff T χ _).mpr
        (T.multiplicativeConductor_spec χ))
    · exact (T.multiplicativeTrivialAt_iff_conductor_le χ m).mp
        ((quasiCharTrivialOnUnitFiltration_iff T χ m).mp h.1)
  · rintro rfl
    refine ⟨(quasiCharTrivialOnUnitFiltration_iff T χ _).mpr
      (T.multiplicativeConductor_spec χ), ?_⟩
    intro r hr
    exact (T.multiplicativeTrivialAt_iff_conductor_le χ r).mp
      ((quasiCharTrivialOnUnitFiltration_iff T χ r).mp hr)

end Langlands.FML.Padic
