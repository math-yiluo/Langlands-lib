import Langlands.HarmonicAnalysis.UnboundedConductorStatement
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Discrete character separation and openness of principal units

Shared helpers extracted unchanged from `UnboundedConductorProof`.
-/

noncomputable section

open scoped WithZero
open Topology

namespace Langlands.HarmonicAnalysis.CharacterSeparation

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

theorem exists_discrete_character {G : Type*} [CommGroup G]
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

theorem principalUnits_isOpen {p : ℕ} [Fact p.Prime]
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

end Langlands.HarmonicAnalysis.CharacterSeparation
