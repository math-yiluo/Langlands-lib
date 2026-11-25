import Langlands.FieldTheory.AbsoluteGaloisOrbitField
import Langlands.GroupScheme.Rational.AdjointHasseCenterReduction
import Langlands.GroupScheme.Torus.WeilTorsionCharacterComparison
import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableHom
import Langlands.Representation.Smooth.Transfer.StabilizerProof
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Number-field kernel models for cyclic absolute characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.AbsoluteGalois

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace characterLattice

variable {k : Type u} [Field k] (Z : CommGroupScheme (Spec (CommRingCat.of k)))

local notation "Ω" => SeparableClosure k
local notation "Γ" => (SeparableClosure k ≃ₐ[k] SeparableClosure k)
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k Ω)
local notation "X" => characterLattice (Functor.obj (BC) Z)

/-- The canonical action on the underlying set of absolute characters. -/
abbrev absoluteMulAction : MulAction Γ X where
  smul σ x := galoisRepresentation k Ω Z σ x
  one_smul x := by change galoisRepresentation k Ω Z 1 x = x; simp
  mul_smul σ τ x := by
    change galoisRepresentation k Ω Z (σ * τ) x =
      galoisRepresentation k Ω Z σ (galoisRepresentation k Ω Z τ x)
    simp

attribute [local instance] absoluteMulAction

/-- The stabilizer of an absolute character of a multiplicative-type group is open. -/
theorem absoluteCharacterStabilizer_isOpen (hZ : IsMultiplicativeType Z.toGrp) (x : X) :
    IsOpen (MulAction.stabilizer Γ x : Set Γ) :=
  (isSmoothVector_iff_isOpen_stabilizer (ρ := galoisRepresentation k Ω Z) x).mp
    (multiplicativeTypeAbsoluteCharacterSmooth k Z hZ x)

end characterLattice

namespace HasNumberFieldCentralKernelModel

variable {k : Type u} [Field k] {Z : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "Ω" => SeparableClosure k
local notation "Γ" => (SeparableClosure k ≃ₐ[k] SeparableClosure k)
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k Ω)
local notation "X" => characterLattice (Functor.obj (BC) Z)
local notation "ρ" => characterLattice.galoisRepresentation k Ω Z

/-- A trivial action with split cyclic coordinates gives the actual split
product kernel model. -/
theorem of_constant_character_coordinates (hZ : IsMultiplicativeType Z.toGrp)
    {I : Type u} [Finite I] {n : ℕ} (hn : 0 < n)
    (e : (I → ZMod n) ≃+ X)
    (hfix : ∀ (σ : Γ) (x : X), ρ σ x = x) :
    HasNumberFieldCentralKernelModel Z.toGrp := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : NeZero n := ⟨hn.ne'⟩
  let eZ := characterLattice.isoOfConstantAbsoluteEquiv hZ e (fun σ m => hfix σ (e m))
  exact Or.inr (Or.inl ⟨I, inferInstance, fun _ => n, fun _ => hn,
    ⟨MultiplicativeTypeGaloisExactness.grpIso eZ ≪≫
      HomScheme.FiniteDiagonalizable.diagonalizableIso k I n⟩⟩)

attribute [local instance] characterLattice.absoluteMulAction

/-- A cyclic absolute character group acted on by sign has a split product
model when the action is trivial and a quadratic norm-one torsion model otherwise. -/
theorem of_cyclic_sign [NumberField k] (hZ : IsMultiplicativeType Z.toGrp)
    {n : ℕ} (hn : 0 < n) (e : ZMod n ≃+ X)
    (hsign : ∀ σ : Γ, (∀ x : X, ρ σ x = x) ∨ (∀ x : X, ρ σ x = -x)) :
    HasNumberFieldCentralKernelModel Z.toGrp := by
  classical
  by_cases hfix : ∀ (σ : Γ) (x : X), ρ σ x = x
  · exact of_constant_character_coordinates hZ hn
      ((AddEquiv.piUnique (fun _ : PUnit.{u + 1} => ZMod n)).trans e) hfix
  let x := e 1
  have hgen (y : X) : ∃ c : ℤ, c • x = y := by
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
    exact ⟨a, by rw [← map_zsmul]; simp⟩
  have hmoved : ∃ σ : Γ, ρ σ x ≠ x := by
    by_contra h
    push Not at h
    apply hfix
    intro σ y
    obtain ⟨c, rfl⟩ := hgen y
    rw [map_smul, h σ]
  obtain ⟨σ, hσ⟩ := hmoved
  have hneg : ρ σ x = -x := (hsign σ).resolve_left (fun h => hσ (h x)) x
  have hne : x ≠ -x := fun he => hσ (hneg.trans he.symm)
  have hnegmem : -x ∈ MulAction.orbit Γ x := MulAction.mem_orbit_iff.mpr ⟨σ, hneg⟩
  have horbit : MulAction.orbit Γ x = {x, -x} := by
    ext y
    constructor
    · rintro ⟨τ, rfl⟩
      rcases hsign τ with h | h <;> simp [show τ • x = ρ τ x from rfl, h x]
    · intro hy
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · exact MulAction.mem_orbit_self (M := Γ) x
      · rwa [Set.mem_singleton_iff.mp hy]
  have hop := characterLattice.absoluteCharacterStabilizer_isOpen Z hZ x
  let B := orbitField (k := k) x
  have hB : Module.finrank k B = 2 := by
    rw [show Module.finrank k B = Nat.card (MulAction.orbit Γ x) from finrank_orbitField x hop,
      horbit, Nat.card_coe_set_eq, Set.ncard_pair hne]
  let : FiniteDimensional k B := Module.finite_of_finrank_pos (by rw [hB]; decide)
  let : NumberField B := NumberField.of_module_finite k B
  let orb := orbitFieldEmbeddingEquiv x hop
  let w (t : B →ₐ[k] Ω) : X := (orb t).val
  have hw (τ : Γ) (t : B →ₐ[k] Ω) : w (τ.toAlgHom.comp t) = ρ τ (w t) :=
    orbitFieldEmbeddingEquiv_comp x hop τ t
  have hpow (t : B →ₐ[k] Ω) : (n : ℤ) • w t = 0 := by
    obtain ⟨a, ha⟩ := e.surjective (w t)
    rw [← ha, ← map_zsmul, ← map_zero e]
    apply congrArg e
    rw [← Int.cast_smul_eq_zsmul (ZMod n), Int.cast_natCast, ZMod.natCast_self, zero_smul]
  let t₀ := orb.symm ⟨x, MulAction.mem_orbit_self (M := Γ) x⟩
  let t₁ := orb.symm ⟨-x, hnegmem⟩
  have ht₀ : w t₀ = x := congrArg Subtype.val (orb.apply_symm_apply _)
  have ht₁ : w t₁ = -x := congrArg Subtype.val (orb.apply_symm_apply _)
  have ht : t₀ ≠ t₁ := fun h => hne (ht₀.symm.trans ((congrArg w h).trans ht₁))
  have hsum : ∑ t, w t = 0 := by
    have hall : ({t₀, t₁} : Finset (B →ₐ[k] Ω)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_pair ht, WeilGm.separableEmbedding_card k B Ω
        (WeilGm.separable_minpoly_splits k B Ω), hB]
    rw [← hall, Finset.sum_pair ht, ht₀, ht₁, add_neg_cancel]
  have hsurj : Function.Surjective (integralCharacterCombination w) := by
    intro y
    obtain ⟨c, rfl⟩ := hgen y
    exact ⟨c • Pi.single t₀ 1, by rw [map_smul, integralCharacterCombination_single, ht₀]⟩
  have hcard : Nat.card X = n ^ (Module.finrank k B - 1) := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_zmod, hB]
    exact (pow_one n).symm
  exact Or.inr (Or.inr (Or.inr ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    n, hn, Or.inl hB, ⟨WeilGm.isoNormOneTorsion_of_characters k B hZ hn w hpow hw hsum hsurj hcard⟩⟩))

private theorem zmod_unit_eq_one_or_neg_one {n : ℕ} (hn : 0 < n) (hsmall : n ≤ 4) :
    ∀ a b : ZMod n, a * b = 1 → a = 1 ∨ a = -1 := by
  interval_cases n <;> decide

private theorem surjective_zmod_hom_sign {n : ℕ} (hn : 0 < n) (hsmall : n ≤ 4)
    (f : ZMod n →+ ZMod n) (hf : Function.Surjective f) :
    (∀ a, f a = a) ∨ (∀ a, f a = -a) := by
  have he (a : ZMod n) : f a = a * f 1 := by
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
    rw [← zsmul_one, map_zsmul, zsmul_one, ← Int.cast_smul_eq_zsmul (ZMod n), smul_eq_mul]
  obtain ⟨b, hb⟩ := hf 1
  have hh : f 1 * b = 1 := by rw [mul_comm, ← he, hb]
  rcases zmod_unit_eq_one_or_neg_one hn hsmall _ _ hh with h | h
  · left
    intro a
    rw [he, h, mul_one]
  · right
    intro a
    rw [he, h, mul_neg, mul_one]

/-- A cyclic group of at most four geometric characters has a model because
each additive automorphism is the identity or negation. -/
theorem of_small_cyclic [NumberField k] (hZ : IsMultiplicativeType Z.toGrp)
    (hc : IsAddCyclic X) {n : ℕ} (hn : 0 < n) (hsmall : n ≤ 4) (hcard : Nat.card X = n) :
    HasNumberFieldCentralKernelModel Z.toGrp := by
  let : IsAddCyclic X := hc
  let e : ZMod n ≃+ X := addEquivOfAddCyclicCardEq ((Nat.card_zmod n).trans hcard.symm)
  apply of_cyclic_sign hZ hn e
  intro σ
  let f : ZMod n →+ ZMod n := e.symm.toAddMonoidHom.comp
    ((ρ σ).toAddMonoidHom.comp e.toAddMonoidHom)
  have hfs : Function.Surjective f := by
    intro a
    refine ⟨e.symm (ρ σ⁻¹ (e a)), ?_⟩
    change e.symm (ρ σ (e (e.symm (ρ σ⁻¹ (e a))))) = a
    rw [e.apply_symm_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    exact e.symm_apply_apply a
  rcases surjective_zmod_hom_sign hn hsmall f hfs with h | h
  · left
    intro a
    obtain ⟨b, rfl⟩ := e.surjective a
    apply e.symm.injective
    exact (h b).trans (e.symm_apply_apply b).symm
  · right
    intro a
    obtain ⟨b, rfl⟩ := e.surjective a
    apply e.symm.injective
    rw [AddEquiv.map_neg, e.symm_apply_apply]
    exact h b

end HasNumberFieldCentralKernelModel

end Langlands.GroupScheme
