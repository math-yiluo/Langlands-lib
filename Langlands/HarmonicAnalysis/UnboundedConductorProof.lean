import Langlands.HarmonicAnalysis.CharacterSeparation

/-! # Continuous quasicharacters with arbitrarily large conductor -/

noncomputable section

open scoped WithZero
open Topology

namespace Langlands.HarmonicAnalysis

private theorem exists_strict_principal_unit {p : ℕ} [Fact p.Prime]
    {F : PadicField p} (T : F.TopologicalData) (n : ℕ) (hn : 0 < n) :
    ∃ u ∈ T.principalUnits n, u ∉ T.principalUnits (n + 1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-(n : ℤ))))
  have hxv : T.discreteValuation x = WithZero.exp (-(n : ℤ)) := by
    change e (ValuativeRel.valuation F.Carrier x) = _
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
  let u : F.Carrierˣ := Units.mk0 (1 + x) hne
  have hu : T.discreteValuation ((u : F.Carrier) - 1) =
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
  intro p hp F A
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨u, hu, hun⟩ := exists_strict_principal_unit T (A + 1) (by omega)
  let H := T.principalUnits (A + 1 + 1)
  let : DiscreteTopology (F.Carrierˣ ⧸ H) :=
    QuotientGroup.discreteTopology (CharacterSeparation.principalUnits_isOpen T _)
  have hq : (QuotientGroup.mk' H) u ≠ 1 := by
    intro h
    exact hun ((QuotientGroup.eq_one_iff u).mp h)
  obtain ⟨c, hc⟩ := CharacterSeparation.exists_discrete_character ((QuotientGroup.mk' H) u) hq
  let q : F.Carrierˣ →ₜ* F.Carrierˣ ⧸ H :=
    { QuotientGroup.mk' H with continuous_toFun := QuotientGroup.continuous_mk }
  let χ : Quasicharacter F.Carrier := c.comp q
  have hχ : χ u ≠ 1 := hc
  refine ⟨χ, ?_⟩
  change A ≤ T.multiplicativeConductor χ
  have hnot : ¬T.multiplicativeConductor χ ≤ A + 1 := by
    intro h
    exact hχ ((T.multiplicativeTrivialAt_iff_conductor_le χ (A + 1)).mpr h u hu)
  omega

end Langlands.HarmonicAnalysis
