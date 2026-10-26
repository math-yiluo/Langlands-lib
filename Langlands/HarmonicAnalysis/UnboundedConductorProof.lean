import Langlands.HarmonicAnalysis.UnboundedConductorStatement
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Continuous quasicharacters with arbitrarily large conductor -/

noncomputable section

open scoped WithZero
open Topology

namespace Langlands.HarmonicAnalysis

private def rationalCircleMap : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map (AddSubgroup.zmultiples (1 : ℚ))
    (AddSubgroup.zmultiples (1 : ℝ)) (Rat.castHom ℝ).toAddMonoidHom (by
      rintro x ⟨n, rfl⟩
      exact ⟨n, by simp⟩)

private theorem rationalCircleMap_injective : Function.Injective rationalCircleMap := by
  apply (injective_iff_map_eq_zero _).2
  intro a ha
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ)) a
  change ((q : ℝ) : AddCircle (1 : ℝ)) = 0 at ha
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 ha
  apply (AddCircle.coe_eq_zero_iff _).2
  refine ⟨n, ?_⟩
  simp only [zsmul_one] at hn ⊢
  exact_mod_cast hn

private theorem exists_discrete_character {G : Type*} [CommGroup G]
    [TopologicalSpace G] [DiscreteTopology G] (g : G) (hg : g ≠ 1) :
    ∃ χ : G →ₜ* ℂˣ, χ g ≠ 1 := by
  have ha : Additive.ofMul g ≠ (0 : Additive G) := hg
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  let φ : G →* ℂˣ :=
    { toFun := fun x =>
        Circle.toUnits (AddCircle.toCircle (rationalCircleMap (c (Additive.ofMul x))))
      map_one' := by simp
      map_mul' := by
        intro x y
        change Circle.toUnits (AddCircle.toCircle
          (rationalCircleMap (c (Additive.ofMul x + Additive.ofMul y)))) = _
        simp only [map_add, AddCircle.toCircle_add, map_mul] }
  refine ⟨{ φ with continuous_toFun := continuous_of_discreteTopology }, ?_⟩
  intro h
  have hz : AddCircle.toCircle (rationalCircleMap (c (Additive.ofMul g))) = 1 :=
    Subtype.ext (congrArg Units.val h)
  apply hc
  apply rationalCircleMap_injective
  apply AddCircle.injective_toCircle one_ne_zero
  simpa only [map_zero, AddCircle.toCircle_zero] using hz

private theorem principalUnits_isOpen {p : ℕ} [Fact p.Prime]
    {F : PadicField p} (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen (T.principalUnits n : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have hval : IsOpen {x : F.Carrier | T.discreteValuation x = 1} := by
    convert (Valuation.isOpen_sphere (v := ValuativeRel.valuation F.Carrier)
      one_ne_zero) using 1
    ext x
    simp only [Set.mem_ofPred_eq, Valuation.restrict_eq_one_iff]
    change e (ValuativeRel.valuation F.Carrier x) = 1 ↔
      ValuativeRel.valuation F.Carrier x = 1
    constructor
    · intro h
      exact e.strictMono.injective (h.trans (map_one e).symm)
    · intro h
      rw [h, map_one]
  have hint : IsOpen (T.Integers : Set F.Carrier) := Valuation.isOpen_integer
  convert (hval.preimage Units.continuous_val).inter
    (hint.preimage ((Units.continuous_val.sub continuous_const).div_const
      (T.uniformizer ^ (n : ℤ)))) using 1
  ext u
  exact T.mem_principalUnits_iff_div_mem_integers n u

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
    QuotientGroup.discreteTopology (principalUnits_isOpen T _)
  have hq : (QuotientGroup.mk' H) u ≠ 1 := by
    intro h
    exact hun ((QuotientGroup.eq_one_iff u).mp h)
  obtain ⟨c, hc⟩ := exists_discrete_character ((QuotientGroup.mk' H) u) hq
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
