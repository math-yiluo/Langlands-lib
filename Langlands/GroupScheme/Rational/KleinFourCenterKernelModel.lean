import Langlands.GroupScheme.Rational.CyclicCenterKernelModel
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.LinearAlgebra.Pi

/-! # Number-field kernel models for an absolute character group of exponent two -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.AbsoluteGalois

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HasNumberFieldCentralKernelModel

variable {k : Type u} [Field k] {Z : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "Ω" => SeparableClosure k
local notation "Γ" => (SeparableClosure k ≃ₐ[k] SeparableClosure k)
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k Ω)
local notation "X" => characterLattice (Functor.obj (BC) Z)
local notation "ρ" => characterLattice.galoisRepresentation k Ω Z

attribute [local instance] characterLattice.absoluteMulAction

private theorem kleinFour_characterCombination_surjective {I : Type u} [Fintype I]
    [IsAddKleinFour X] (w : I → X) (i j : I)
    (hi : w i ≠ 0) (hj : w j ≠ 0) (hij : w i ≠ w j) :
    Function.Surjective (integralCharacterCombination w) := by
  classical
  let f := integralCharacterCombination w
  have hwi : w i ∈ f.range := ⟨Pi.single i 1, integralCharacterCombination_single w i⟩
  have hwj : w j ∈ f.range := ⟨Pi.single j 1, integralCharacterCombination_single w j⟩
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro z _
  by_cases hz : z = 0
  · subst z
    exact f.range.zero_mem
  by_cases hzi : z = w i
  · rwa [hzi]
  by_cases hzj : z = w j
  · rwa [hzj]
  rw [IsAddKleinFour.eq_add_of_ne_all hi hj hij hz hzi hzj]
  exact f.range.add_mem hwi hwj

/-- A group of multiplicative type with Klein four absolute characters
has a split, a quadratic Weil torsion or a cubic norm-one torsion model. -/
theorem of_kleinFour [NumberField k] (hZ : IsMultiplicativeType Z.toGrp) (hX : IsAddKleinFour X) :
    HasNumberFieldCentralKernelModel Z.toGrp := by
  classical
  let : IsAddKleinFour X := hX
  let : Finite X := Nat.finite_of_card_ne_zero (hX.card_four.trans_ne (by decide))
  by_cases hfix : ∀ (σ : Γ) (x : X), ρ σ x = x
  · obtain ⟨e⟩ : Nonempty ((ZMod 2 × ZMod 2) ≃+ X) := IsAddKleinFour.nonempty_addEquiv
    let eI : (ULift.{u} (Fin 2) → ZMod 2) ≃ₗ[ℤ] (Fin 2 → ZMod 2) :=
      LinearEquiv.funCongrLeft ℤ (ZMod 2) Equiv.ulift.symm
    exact of_constant_character_coordinates hZ (show 0 < 2 by decide)
      (eI.toAddEquiv.trans ((LinearEquiv.finTwoArrow ℤ (ZMod 2)).toAddEquiv.trans e)) hfix
  push Not at hfix
  obtain ⟨τ, x, hτ⟩ := hfix
  let y := ρ τ x
  have hxy : x ≠ y := hτ.symm
  have hx : x ≠ 0 := by
    rintro rfl
    exact hτ (map_zero (ρ τ))
  have hnonzero {z : X} (hz : z ∈ MulAction.orbit Γ x) : z ≠ 0 := by
    obtain ⟨σ, rfl⟩ := MulAction.mem_orbit_iff.mp hz
    change ρ σ x ≠ 0
    intro h
    have h' := congrArg (ρ σ⁻¹) h
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h'
    exact hx h'
  let x₀ : MulAction.orbit Γ x := ⟨x, MulAction.mem_orbit_self (M := Γ) x⟩
  let x₁ : MulAction.orbit Γ x := ⟨y, MulAction.mem_orbit_iff.mpr ⟨τ, rfl⟩⟩
  have hlo : 1 < Nat.card (MulAction.orbit Γ x) := by
    let : Nontrivial (MulAction.orbit Γ x) := ⟨⟨x₀, x₁, fun h => hxy (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hcard₃ : Nat.card {z : X // z ≠ 0} = 3 := by
    let : Fintype X := Fintype.ofFinite X
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun z : X => z = 0),
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hX.card_four]
  have hhi : Nat.card (MulAction.orbit Γ x) ≤ 3 := by
    rw [← hcard₃]
    let i : MulAction.orbit Γ x → {z : X // z ≠ 0} := fun a => ⟨a.val, hnonzero a.property⟩
    exact Nat.card_le_card_of_injective i
      (fun _ _ h => Subtype.ext (congrArg (fun z : {z : X // z ≠ 0} => z.val) h))
  have hopen := characterLattice.absoluteCharacterStabilizer_isOpen Z hZ x
  let B := orbitField (k := k) x
  have hdeg : Module.finrank k B = Nat.card (MulAction.orbit Γ x) := finrank_orbitField x hopen
  let : FiniteDimensional k B := Module.finite_of_finrank_pos (by rw [hdeg]; omega)
  let : NumberField B := NumberField.of_module_finite k B
  let e := orbitFieldEmbeddingEquiv x hopen
  let w (t : B →ₐ[k] Ω) : X := (e t).val
  have hw (σ : Γ) (t : B →ₐ[k] Ω) : w (σ.toAlgHom.comp t) = ρ σ (w t) :=
    orbitFieldEmbeddingEquiv_comp x hopen σ t
  have hw_inj : Function.Injective w := fun _ _ h => e.injective (Subtype.ext h)
  have hw_nonzero (t : B →ₐ[k] Ω) : w t ≠ 0 := hnonzero (e t).property
  have hpow (t : B →ₐ[k] Ω) : (2 : ℤ) • w t = 0 := by
    rw [two_zsmul]
    exact IsAddKleinFour.add_self _
  let t₀ := e.symm x₀
  let t₁ := e.symm x₁
  have ht₀ : w t₀ = x := congrArg Subtype.val (e.apply_symm_apply x₀)
  have ht₁ : w t₁ = y := congrArg Subtype.val (e.apply_symm_apply x₁)
  have ht : t₀ ≠ t₁ := fun h => hxy (ht₀.symm.trans ((congrArg w h).trans ht₁))
  have hsurj : Function.Surjective (integralCharacterCombination w) :=
    kleinFour_characterCombination_surjective w t₀ t₁
      (hw_nonzero _) (hw_nonzero _) (hw_inj.ne ht)
  by_cases h2 : Module.finrank k B = 2
  · have hc : Nat.card X = 2 ^ Module.finrank k B := by
      rw [h2, hX.card_four]
      decide
    exact Or.inr (Or.inr (Or.inl ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
      2, by decide, ⟨WeilGm.isoWeilTorsion_of_characters k B hZ (by decide) w hpow hw hsurj hc⟩⟩))
  have h3 : Module.finrank k B = 3 := by omega
  have hE : Fintype.card (B →ₐ[k] Ω) = 3 :=
    (WeilGm.separableEmbedding_card k B Ω (WeilGm.separable_minpoly_splits k B Ω)).trans h3
  have hcardpair : ({t₀, t₁} : Finset (B →ₐ[k] Ω)).card <
      (Finset.univ : Finset (B →ₐ[k] Ω)).card := by
    rw [Finset.card_pair ht, Finset.card_univ, hE]
    decide
  obtain ⟨t₂, _, ht₂⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardpair
  obtain ⟨ht₂₀, ht₂₁⟩ : t₂ ≠ t₀ ∧ t₂ ≠ t₁ := by simpa using ht₂
  have hsum : ∑ t, w t = 0 := by
    have hall : insert t₂ ({t₀, t₁} : Finset (B →ₐ[k] Ω)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_insert_of_notMem ht₂, Finset.card_pair ht, hE]
    have hw₂ : w t₂ = w t₀ + w t₁ := IsAddKleinFour.eq_add_of_ne_all
      (hw_nonzero _) (hw_nonzero _) (hw_inj.ne ht) (hw_nonzero _)
      (hw_inj.ne ht₂₀) (hw_inj.ne ht₂₁)
    rw [← hall, Finset.sum_insert ht₂, Finset.sum_pair ht, hw₂]
    exact IsAddKleinFour.add_self _
  have hc : Nat.card X = 2 ^ (Module.finrank k B - 1) := by
    rw [h3, hX.card_four]
    decide
  have hcoprime : (Module.finrank k B).Coprime 2 := by
    rw [h3]
    decide
  exact Or.inr (Or.inr (Or.inr ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    2, by decide, Or.inr hcoprime,
    ⟨WeilGm.isoNormOneTorsion_of_characters k B hZ (by decide) w hpow hw hsum hsurj hc⟩⟩))

end Langlands.GroupScheme.HasNumberFieldCentralKernelModel

namespace Langlands.GroupScheme

/-- A group of multiplicative type over a number field with four geometric
characters of exponent two has one of the arithmetic kernel models. -/
def NumberFieldKleinFourCentralKernelStatement : Prop :=
  ∀ (k : Type u) [Field k] [NumberField k] (Z : CommGroupScheme (Spec (CommRingCat.of k))),
    IsMultiplicativeType Z.toGrp →
      IsAddKleinFour (characterLattice
        ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj Z)) →
      HasNumberFieldCentralKernelModel Z.toGrp

theorem numberFieldKleinFourCentralKernel : NumberFieldKleinFourCentralKernelStatement.{u} :=
  fun _ _ _ _ => HasNumberFieldCentralKernelModel.of_kleinFour

end Langlands.GroupScheme
