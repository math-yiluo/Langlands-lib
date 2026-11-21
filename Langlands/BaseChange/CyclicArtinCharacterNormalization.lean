import Langlands.HarmonicAnalysis.PadicPrincipalUnitCharacterExtensionProof
import Langlands.ClassFieldTheory.Local.NormExistenceClosedSupport
import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor
import Langlands.AllField.HarmonicAnalysis.ConductorSupplement
import Langlands.LocalField.PadicBridge

/-! # Finite-order representatives for the conductor of a norm pullback -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open HarmonicAnalysis

universe u v

section Conductor

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- The bundled unit-congruence level equals the level in the underlying local field. -/
theorem toLocalFieldData_principalUnits (n : ℕ) :
    T.toLocalFieldData.principalUnits n = T.principalUnits n := by
  ext a
  rfl

/-- The two actual principal-unit filtrations define the same multiplicative conductor. -/
theorem toLocalFieldData_multiplicativeConductor :
    letI := T.topology
    ∀ χ : Quasicharacter F.Carrier,
      T.toLocalFieldData.multiplicativeConductor χ = T.multiplicativeConductor χ := by
  let := T.topology
  intro χ
  apply le_antisymm
  · apply (T.toLocalFieldData.multiplicativeTrivialAt_iff_conductor_le _ _).mp
    intro a ha
    rw [T.toLocalFieldData_principalUnits] at ha
    exact T.multiplicativeConductor_spec χ a ha
  · apply (T.multiplicativeTrivialAt_iff_conductor_le _ _).mp
    intro a ha
    rw [← T.toLocalFieldData_principalUnits] at ha
    exact T.toLocalFieldData.multiplicativeConductor_spec χ a ha

/-- Agreement on integral units implies equality of all conductor comparisons. -/
theorem multiplicativeConductor_eq_of_eqOn_unitSubgroup :
    letI := T.topology
    ∀ χ χ' : Quasicharacter F.Carrier,
      (∀ a ∈ T.unitSubgroup, χ a = χ' a) →
      T.multiplicativeConductor χ = T.multiplicativeConductor χ' := by
  let := T.topology
  intro χ χ' h
  have hlev (n : ℕ) : T.MultiplicativeTrivialAt χ n ↔ T.MultiplicativeTrivialAt χ' n := by
    have hui : T.principalUnits n ≤ T.unitSubgroup := by
      rw [← T.unitFiltration_zero, T.unitFiltration_eq_principalUnits]
      exact T.principalUnits_antitone (Nat.zero_le n)
    exact forall₂_congr fun a ha => by rw [h a (hui ha)]
  exact le_antisymm
    ((T.multiplicativeTrivialAt_iff_conductor_le _ _).mp
      ((hlev _).mpr (T.multiplicativeConductor_spec χ')))
    ((T.multiplicativeTrivialAt_iff_conductor_le _ _).mp
      ((hlev _).mp (T.multiplicativeConductor_spec χ)))

/-- Every quasicharacter has a finite-order representative with the same
values on the full integral-unit subgroup. -/
theorem exists_finiteOrder_eqOn_unitSubgroup :
    letI := T.topology
    ∀ χ : Quasicharacter F.Carrier,
      ∃ χ' : Quasicharacter F.Carrier, (∃ m : ℕ, 0 < m ∧ χ' ^ m = 1) ∧
        ∀ a ∈ T.unitSubgroup, χ' a = χ a := by
  let := T.topology
  intro χ
  let j : T.principalUnits 0 →ₜ* F.Carrierˣ :=
    { toMonoidHom := (T.principalUnits 0).subtype
      continuous_toFun := continuous_subtype_val }
  obtain ⟨χ', hfinite, hχ', _⟩ := padicPrincipalUnitCharacterExtension p F T 0 (χ.comp j)
  refine ⟨χ', hfinite, fun a ha => ?_⟩
  rw [← T.unitFiltration_zero, T.unitFiltration_eq_principalUnits] at ha
  exact hχ' ⟨a, ha⟩

end Conductor

section Norm

open LocalClassField
open ClassFieldTheory.Local (mem_unitSubgroup_iff_ord_eq_zero)

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  (T : F.TopologicalData) (S : E.TopologicalData)

/-- The actual determinant norm sends integral units to integral units. -/
theorem localNorm_mem_unitSubgroup :
    letI := T.topology
    letI := S.topology
    ∀ {a : E.Carrierˣ}, a ∈ S.unitSubgroup → localNorm T S a ∈ T.unitSubgroup := by
  let := T.topology
  let := S.topology
  let : FiniteDimensional F.Carrier E.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) F.Carrier E.Carrier
  intro a ha
  apply (mem_unitSubgroup_iff_ord_eq_zero F T _).mpr
  apply (ord_relative_norm_units_eq_zero_iff F E T S a).mpr
  exact (mem_unitSubgroup_iff_ord_eq_zero E S a).mp ha

/-- The finite-order normalization at the base preserves the conductors of
all continuous twists and the conductor of the norm pullback. -/
theorem exists_finiteOrder_preserving_twist_and_norm_conductors :
    letI := T.topology
    letI := S.topology
    letI := T.valuativeRel
    letI := S.valuativeRel
    letI := T.localField
    letI := S.localField
    ∀ χ : Quasicharacter F.Carrier,
      ∃ χ' : Quasicharacter F.Carrier, (∃ m : ℕ, 0 < m ∧ χ' ^ m = 1) ∧
        (∀ κ : Quasicharacter F.Carrier,
          (LocalFieldData.ofInstances F.Carrier).multiplicativeConductor (κ * χ) =
            T.multiplicativeConductor (κ * χ')) ∧
        (LocalFieldData.ofInstances E.Carrier).multiplicativeConductor (χ.comp (localNorm T S)) =
          S.multiplicativeConductor (χ'.comp (localNorm T S)) := by
  let := T.topology
  let := S.topology
  let := T.valuativeRel
  let := S.valuativeRel
  let := T.localField
  let := S.localField
  intro χ
  obtain ⟨χ', hfinite, h⟩ := T.exists_finiteOrder_eqOn_unitSubgroup χ
  refine ⟨χ', hfinite, fun κ => ?_, ?_⟩
  · change T.toLocalFieldData.multiplicativeConductor (κ * χ) = _
    rw [T.toLocalFieldData_multiplicativeConductor]
    apply T.multiplicativeConductor_eq_of_eqOn_unitSubgroup
    intro a ha
    simp only [ContinuousMonoidHom.mul_apply, h a ha]
  · change S.toLocalFieldData.multiplicativeConductor (χ.comp (localNorm T S)) = _
    refine (S.toLocalFieldData_multiplicativeConductor (χ.comp (localNorm T S))).trans ?_
    apply S.multiplicativeConductor_eq_of_eqOn_unitSubgroup
    intro a ha
    exact (h (localNorm T S a) (T.localNorm_mem_unitSubgroup S ha)).symm

end Norm

end Langlands.PadicField.TopologicalData
