import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement
import Langlands.HarmonicAnalysis.CharacterTransport
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Existence of a nontrivial unitary additive character of a p-adic field

A character of `ℚ_p ⧸ ℤ_p` that is nontrivial at the class of `p⁻¹` gives a
continuous nontrivial unitary additive character of `ℚ_p`. Its trace pullback is
a character of every supplied p-adic field realization.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis

universe u

namespace PadicAdditiveCharacter

/-- The inclusion `ℚ/ℤ → ℝ/ℤ`. -/
private def ratCircleToRealCircle : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map (AddSubgroup.zmultiples (1 : ℚ))
    (AddSubgroup.zmultiples (1 : ℝ)) (Rat.castHom ℝ).toAddMonoidHom (by
      rintro x ⟨n, rfl⟩
      exact ⟨n, by simp⟩)

private theorem ratCircleToRealCircle_injective :
    Function.Injective ratCircleToRealCircle := by
  apply (injective_iff_map_eq_zero _).2
  intro a ha
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ)) a
  change ((q : ℝ) : AddCircle (1 : ℝ)) = 0 at ha
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 ha
  apply (AddCircle.coe_eq_zero_iff _).2
  refine ⟨n, ?_⟩
  simp only [zsmul_one] at hn ⊢
  exact_mod_cast hn

/-- An additive character of any additive group with values in `ℚ/ℤ`, viewed in
the unit circle through `t ↦ exp(2πit)`. -/
private def toCircleAddChar {A : Type*} [AddCommGroup A] (c : A →+ AddCircle (1 : ℚ)) :
    AddChar A Circle where
  toFun a := AddCircle.toCircle (ratCircleToRealCircle (c a))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp only [map_add, AddCircle.toCircle_add]

private theorem toCircleAddChar_apply_eq_one_iff {A : Type*} [AddCommGroup A]
    (c : A →+ AddCircle (1 : ℚ)) (a : A) :
    toCircleAddChar c a = 1 ↔ c a = 0 := by
  constructor
  · intro h
    apply ratCircleToRealCircle_injective
    apply AddCircle.injective_toCircle one_ne_zero
    rw [map_zero, AddCircle.toCircle_zero]
    exact h
  · intro h
    change AddCircle.toCircle (ratCircleToRealCircle (c a)) = 1
    rw [h, map_zero, AddCircle.toCircle_zero]

/-- The p-adic integers `ℤ_p = {x : ‖x‖ ≤ 1}` as an additive subgroup of `ℚ_p`. -/
private def padicIntegers (p : ℕ) [Fact p.Prime] : AddSubgroup ℚ_[p] :=
  (PadicInt.subring p).toAddSubgroup

private theorem isOpen_padicIntegers (p : ℕ) [Fact p.Prime] :
    IsOpen (padicIntegers p : Set ℚ_[p]) := by
  change IsOpen {y : ℚ_[p] | ‖y‖ ≤ 1}
  simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
    IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero

private theorem inv_p_not_mem_padicIntegers (p : ℕ) [Fact p.Prime] :
    ((p : ℚ_[p])⁻¹) ∉ padicIntegers p := by
  change ¬ ‖((p : ℚ_[p])⁻¹)‖ ≤ 1
  rw [norm_inv, Padic.norm_p, inv_inv, not_le]
  exact_mod_cast (Fact.out : p.Prime).one_lt

end PadicAdditiveCharacter

open PadicAdditiveCharacter in
/-- `ℚ_p`, with its usual topology, carries a continuous unitary additive
character that is trivial on `ℤ_p` and nontrivial at `p⁻¹`. -/
theorem exists_padic_unitaryAdditiveCharacter (p : ℕ) [Fact p.Prime] :
    ∃ ψ : UnitaryAdditiveCharacter ℚ_[p],
      (∀ z : ℤ_[p], ψ (z : ℚ_[p]) = 1) ∧ ψ ((p : ℚ_[p])⁻¹) ≠ 1 := by
  let L := padicIntegers p
  have hx : (QuotientAddGroup.mk ((p : ℚ_[p])⁻¹) : ℚ_[p] ⧸ L) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact inv_p_not_mem_padicIntegers p
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hx
  let c' : (ℚ_[p] ⧸ L) →+ AddCircle (1 : ℚ) := c
  let χ : AddChar ℚ_[p] Circle := toCircleAddChar (c'.comp (QuotientAddGroup.mk' L))
  have hdisc : DiscreteTopology (ℚ_[p] ⧸ L) :=
    QuotientAddGroup.discreteTopology (isOpen_padicIntegers p)
  have hcont : Continuous χ := by
    change Continuous ((fun q : ℚ_[p] ⧸ L =>
      AddCircle.toCircle (ratCircleToRealCircle (c' q))) ∘ QuotientAddGroup.mk)
    exact continuous_of_discreteTopology.comp QuotientAddGroup.continuous_mk
  have hne : χ ((p : ℚ_[p])⁻¹) ≠ 1 := by
    rw [Ne, toCircleAddChar_apply_eq_one_iff]
    exact hc
  refine ⟨⟨χ, hcont, fun h => hne (by rw [h, AddChar.one_apply])⟩, ?_, hne⟩
  intro z
  change χ (z : ℚ_[p]) = 1
  rw [toCircleAddChar_apply_eq_one_iff]
  change c' (QuotientAddGroup.mk (z : ℚ_[p])) = 0
  rw [(QuotientAddGroup.eq_zero_iff (z : ℚ_[p])).2 z.2, map_zero]

/-- Every supplied topological realization of a finite extension of `ℚ_p`
carries a continuous nontrivial unitary additive character. -/
theorem padicUnitaryAdditiveCharacterExists {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) :
    PadicUnitaryAdditiveCharacterExistsStatement F T := by
  obtain ⟨ψ, -, -⟩ := exists_padic_unitaryAdditiveCharacter p
  let _ : Algebra (PadicField.rational p).Carrier F.Carrier := F.algebra
  have : IsScalarTower (Padic p) (PadicField.rational p).Carrier F.Carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨(PadicField.rationalTopologicalData p).traceCharacter T ψ⟩

end Langlands.HarmonicAnalysis
