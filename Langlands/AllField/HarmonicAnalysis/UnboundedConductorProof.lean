import Langlands.HarmonicAnalysis.UnboundedConductorProof
import Langlands.AllField.HarmonicAnalysis.CharacterSeparation
/-! # Continuous quasicharacters with arbitrarily large conductor -/

noncomputable section

open scoped WithZero
open Topology

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicQuasicharacterUnboundedConductorStatement padicQuasicharacterUnboundedConductor
open Langlands.AllField.HarmonicAnalysis

private theorem exists_strict_principal_unit 
    {F : Type*} [Field F] (T : LocalFieldData F) (n : ℕ) (hn : 0 < n) :
    ∃ u ∈ T.principalUnits n, u ∉ T.principalUnits (n + 1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-(n : ℤ))))
  have hxv : T.discreteValuation x = WithZero.exp (-(n : ℤ)) := by
    change e (ValuativeRel.valuation F x) = _
    rw [hx, e.apply_symm_apply]
  have hxlt : T.discreteValuation x < 1 := by
    rw [hxv, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hunit : T.discreteValuation (1 + x) = 1 := by
    simpa using T.discreteValuation.map_add_eq_of_lt_left (x := 1) (y := x)
      (by simpa using hxlt)
  have hne : 1 + x ≠ 0 := by
    intro h
    rw [h, map_zero] at hunit
    exact zero_ne_one hunit
  let u : Fˣ := Units.mk0 (1 + x) hne
  have hu : T.discreteValuation ((u : F) - 1) =
      WithZero.exp (-(n : ℤ)) := by
    simpa [u] using hxv
  refine ⟨u, ⟨hunit, hu.le⟩, ?_⟩
  intro h
  have hle := h.2
  rw [hu] at hle
  have := WithZero.exp_le_exp.mp hle
  omega

universe uF

/-- Canonical p-adic fields have continuous complex quasicharacters with
arbitrarily large multiplicative conductor. -/
theorem padicQuasicharacterUnboundedConductor :
    PadicQuasicharacterUnboundedConductorStatement.{uF} := by
  intro F _ _ _ _ A
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨u, hu, hun⟩ := exists_strict_principal_unit T (A + 1) (by omega)
  let H := T.principalUnits (A + 1 + 1)
  let : DiscreteTopology (Fˣ ⧸ H) :=
    QuotientGroup.discreteTopology (Langlands.AllField.HarmonicAnalysis.CharacterSeparation.principalUnits_isOpen T _)
  have hq : (QuotientGroup.mk' H) u ≠ 1 := by
    intro h
    exact hun ((QuotientGroup.eq_one_iff u).mp h)
  obtain ⟨c, hc⟩ := CharacterSeparation.exists_discrete_character ((QuotientGroup.mk' H) u) hq
  let q : Fˣ →ₜ* Fˣ ⧸ H :=
    { QuotientGroup.mk' H with continuous_toFun := QuotientGroup.continuous_mk }
  let χ : Quasicharacter F := c.comp q
  have hχ : χ u ≠ 1 := hc
  refine ⟨χ, ?_⟩
  change A ≤ T.multiplicativeConductor χ
  have hnot : ¬T.multiplicativeConductor χ ≤ A + 1 := by
    intro h
    exact hχ ((T.multiplicativeTrivialAt_iff_conductor_le χ (A + 1)).mpr h u hu)
  omega

end Langlands.AllField.HarmonicAnalysis
