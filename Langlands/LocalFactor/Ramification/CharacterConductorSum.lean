import Langlands.LocalFactor.SpectralConductorClassFunction
import Langlands.Representation.Twist.Definitions
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Sums over the characters of a finite abelian quotient

The quotient-character sum turns a sum of weighted rank-one character
codimensions into a contribution off the subgroup and a sum on the subgroup.
-/

noncomputable section

namespace Langlands.Ramification

open scoped BigOperators Classical

universe u

variable {G : Type u} [CommGroup G] [Finite G]

local notation "DualSubgroup" => CommGroup.subgroupOrderIsoSubgroupMonoidHom G ℂ

/-- The sum of the values of the characters trivial on `H` is the index of
`H` on `H`, and zero at every other group element. -/
theorem sum_characters_trivial_on (H : Subgroup G) (g : G) :
    letI := Fintype.ofFinite (DualSubgroup H).ofDual
    (∑ κ : (DualSubgroup H).ofDual, (κ.val g : ℂ)) =
      if g ∈ H then (H.index : ℂ) else 0 := by
  classical
  let D := (DualSubgroup H).ofDual
  let : Fintype D := Fintype.ofFinite D
  change (∑ κ : D, (κ.val g : ℂ)) = _
  by_cases hg : g ∈ H
  · rw [ite_eq_left hg]
    have hcard : Fintype.card D = H.index := by
      rw [← Nat.card_eq_fintype_card]
      exact CommGroup.card_subgroupOrderIsoSubgroupMonoidHom ℂ H
    calc
      (∑ κ : D, (κ.val g : ℂ)) = ∑ _ : D, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro κ _
        rw [(CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_iff ℂ H κ.val).mp
          κ.property g hg, Units.val_one]
      _ = (H.index : ℂ) := by simp [hcard]
  · rw [ite_eq_right hg]
    have hex : ∃ κ : D, κ.val g ≠ 1 := by
      by_contra! h
      apply hg
      apply (CommGroup.forall_monoidHom_apply_eq_one_iff ℂ H g).mp
      intro κ hκ
      exact h ⟨κ, (CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_iff ℂ H κ).mpr hκ⟩
    obtain ⟨κ, hκ⟩ := hex
    have hκ' : (κ.val g : ℂ) ≠ 1 := fun h => hκ (Units.ext h)
    have h := Equiv.sum_comp (Equiv.mulLeft κ) (fun θ : D => (θ.val g : ℂ))
    change (∑ θ : D, (((κ * θ).val g : ℂˣ) : ℂ)) = _ at h
    simp only [Subgroup.coe_mul, MonoidHom.mul_apply, Units.val_mul, ← Finset.mul_sum] at h
    have hz : ((κ.val g : ℂ) - 1) * ∑ θ : D, (θ.val g : ℂ) = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hκ')

/-- For any weights, summing the rank-one trace deficits of the twists of
`χ` over the characters of `G/H` retains the trace of `χ` on `H` only. -/
theorem sum_weighted_character_deficits (H : Subgroup G) (S : Finset G)
    (w : G → ℂ) (χ : G →* ℂˣ) :
    letI := Fintype.ofFinite (DualSubgroup H).ofDual
    ∑ κ : (DualSubgroup H).ofDual, ∑ g ∈ S, w g * (1 - ((χ * κ.val) g : ℂ)) =
      (H.index : ℂ) * ∑ g ∈ S, w g * (1 - if g ∈ H then (χ g : ℂ) else 0) := by
  classical
  let D := (DualSubgroup H).ofDual
  let : Fintype D := Fintype.ofFinite D
  change (∑ κ : D, ∑ g ∈ S, w g * (1 - ((χ * κ.val) g : ℂ))) = _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  have hcard : Fintype.card D = H.index := by
    rw [← Nat.card_eq_fintype_card]
    exact CommGroup.card_subgroupOrderIsoSubgroupMonoidHom ℂ H
  have hs := sum_characters_trivial_on H g
  change (∑ κ : D, (κ.val g : ℂ)) = _ at hs
  simp only [MonoidHom.mul_apply, Units.val_mul, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, mul_one, hs]
  split_ifs <;> ring

section ArtinConductor

open LocalFactor.SpectralConductor (artinConductor_eq_classSum lowerCount)

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [MulSemiringAction G R] [FaithfulSMul G R]

private theorem rankOne_artinConductor_eq_classSum {J : Type*} [Group J] [Fintype J]
    [MulSemiringAction J R] [FaithfulSMul J R] (χ : J →* ℂˣ) (b : ℕ)
    (hb : ∀ i ≥ b, lowerGroup R J i = ⊥) :
    (artinConductor R J (characterRepresentation χ) : ℂ) =
      (Nat.card (lowerGroup R J 0) : ℂ)⁻¹ * ∑ g : J,
        (lowerCount R J b g : ℂ) * (1 - (χ g : ℂ)) := by
  classical
  have htrace (g : J) : LinearMap.trace ℂ ℂ (characterRepresentation χ g) = (χ g : ℂ) := by
    change LinearMap.trace ℂ ℂ ((χ g : ℂ) • LinearMap.id) = _
    simp only [map_smul, LinearMap.trace_id, Module.finrank_self, Nat.cast_one, smul_eq_mul, mul_one]
  simp only [artinConductor_eq_classSum R (characterRepresentation χ) b hb,
    Module.finrank_self, Nat.cast_one, htrace]

omit [Finite G] [IsNoetherianRing R] [FaithfulSMul G R] in
private theorem mem_lowerGroup_subtype (H : Subgroup G) (i : ℕ) (g : H) :
    g ∈ lowerGroup R H i ↔ (g : G) ∈ lowerGroup R G i := Iff.rfl

omit [Finite G] [IsNoetherianRing R] [FaithfulSMul G R] in
private theorem lowerCount_subtype (H : Subgroup G) (b : ℕ) (g : H) :
    lowerCount R H b g = lowerCount R G b (g : G) := by
  unfold lowerCount
  congr 1

/-- The sum of Artin conductors of the twists by the characters of `G/H`
is the sum for the quotient characters alone plus the inertia-index
coefficient times the conductor of the restricted character. -/
theorem sum_artinConductor_twists_trivial_on (H : Subgroup G) (χ : G →* ℂˣ) :
    letI := Fintype.ofFinite (DualSubgroup H).ofDual
    ∑ κ : (DualSubgroup H).ofDual, artinConductor R G (characterRepresentation (χ * κ.val)) =
      (∑ κ : (DualSubgroup H).ofDual, artinConductor R G (characterRepresentation κ.val)) +
        ((H.index : ℚ) * Nat.card (lowerGroup R H 0) / Nat.card (lowerGroup R G 0)) *
          artinConductor R H (characterRepresentation (χ.comp H.subtype)) := by
  classical
  let D := (DualSubgroup H).ofDual
  let : Fintype D := Fintype.ofFinite D
  let : Fintype G := Fintype.ofFinite G
  let : Fintype H := Fintype.ofFinite H
  obtain ⟨b, hb⟩ := exists_lowerGroup_eq_bot R G
  have hbH : ∀ i ≥ b, lowerGroup R H i = ⊥ := by
    intro i hi
    ext h
    rw [mem_lowerGroup_subtype, hb i hi, Subgroup.mem_bot, Subgroup.mem_bot]
    exact ⟨fun hh => Subtype.ext hh, fun hh => congrArg Subtype.val hh⟩
  let w (g : G) : ℂ := lowerCount R G b g
  let cG : ℂ := Nat.card (lowerGroup R G 0)
  let cH : ℂ := Nat.card (lowerGroup R H 0)
  have htw (ξ : G →* ℂˣ) :
      (∑ κ : D, (artinConductor R G (characterRepresentation (ξ * κ.val)) : ℂ)) =
        cG⁻¹ * ((H.index : ℂ) * ∑ g : G, w g * (1 - if g ∈ H then (ξ g : ℂ) else 0)) := by
    simp only [rankOne_artinConductor_eq_classSum R _ b hb, ← Finset.mul_sum]
    change cG⁻¹ * (∑ κ : D, ∑ g : G, w g * (1 - ((ξ * κ.val) g : ℂ))) = _
    rw [sum_weighted_character_deficits H Finset.univ w ξ]
  have h1 := htw 1
  have hone (κ : G →* ℂˣ) : (1 : G →* ℂˣ) * κ = κ :=
    MonoidHom.ext fun _ => one_mul _
  simp only [hone, MonoidHom.one_apply, Units.val_one] at h1
  have hH : (artinConductor R H (characterRepresentation (χ.comp H.subtype)) : ℂ) =
      cH⁻¹ * ∑ h : H, w (h : G) * (1 - (χ (h : G) : ℂ)) := by
    rw [rankOne_artinConductor_eq_classSum R _ b hbH]
    simp only [lowerCount_subtype, MonoidHom.comp_apply, Subgroup.subtype_apply, w, cH]
  have hS : (∑ h : H, w (h : G) * (1 - (χ (h : G) : ℂ))) =
      ∑ g : G, if g ∈ H then w g * (1 - (χ g : ℂ)) else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) (fun g => w g * (1 - (χ g : ℂ)))).symm
  have hsplit :
      (∑ g : G, w g * (1 - if g ∈ H then (χ g : ℂ) else 0)) =
        (∑ g : G, w g * (1 - if g ∈ H then (1 : ℂ) else 0)) +
          ∑ h : H, w (h : G) * (1 - (χ (h : G) : ℂ)) := by
    rw [hS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> ring
  change (∑ κ : D, artinConductor R G (characterRepresentation (χ * κ.val))) = _
  apply (Rat.cast_injective (α := ℂ))
  push_cast
  rw [htw, h1, hH, hsplit]
  have hne : cH ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  change _ = _ + ((H.index : ℂ) * cH / cG) * _
  field_simp [hne]

omit [IsNoetherianRing R] in
private theorem sum_lowerCount_eq_sum_card {J : Type*} [Group J] [Fintype J]
    [MulSemiringAction J R] (b : ℕ) :
    ∑ g : J, lowerCount R J b g = ∑ i ∈ Finset.range b, Nat.card (lowerGroup R J i) := by
  classical
  simp only [lowerCount, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.card_filter, Nat.card_eq_fintype_card]
  exact (Fintype.card_subtype _).symm

/-- The Artin conductor sum of the characters of `G/H` is the index of `H`
divided by the inertia order, times the sum of differences of the lower
ramification group orders. -/
theorem sum_artinConductor_trivial_on (H : Subgroup G) (b : ℕ)
    (hb : ∀ i ≥ b, lowerGroup R G i = ⊥) :
    letI := Fintype.ofFinite (DualSubgroup H).ofDual
    ∑ κ : (DualSubgroup H).ofDual, artinConductor R G (characterRepresentation κ.val) =
      (H.index : ℚ) / Nat.card (lowerGroup R G 0) * ∑ i ∈ Finset.range b,
        ((Nat.card (lowerGroup R G i) : ℚ) - Nat.card (lowerGroup R H i)) := by
  classical
  let D := (DualSubgroup H).ofDual
  let : Fintype D := Fintype.ofFinite D
  let : Fintype G := Fintype.ofFinite G
  let : Fintype H := Fintype.ofFinite H
  let w (g : G) : ℂ := lowerCount R G b g
  have hS : (∑ h : H, w (h : G)) = ∑ g : G, if g ∈ H then w g else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) w).symm
  have hsplit : (∑ g : G, w g * (1 - if g ∈ H then (1 : ℂ) else 0)) =
      (∑ g : G, w g) - ∑ h : H, w (h : G) := by
    rw [hS, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> ring
  have hG : (∑ g : G, w g) = ∑ i ∈ Finset.range b, (Nat.card (lowerGroup R G i) : ℂ) := by
    unfold w
    exact_mod_cast sum_lowerCount_eq_sum_card (J := G) R b
  have hH : (∑ h : H, w (h : G)) =
      ∑ i ∈ Finset.range b, (Nat.card (lowerGroup R H i) : ℂ) := by
    simp only [w, ← lowerCount_subtype R H b]
    exact_mod_cast sum_lowerCount_eq_sum_card (J := H) R b
  have horth := sum_weighted_character_deficits H Finset.univ w (1 : G →* ℂˣ)
  have hone (κ : G →* ℂˣ) : (1 : G →* ℂˣ) * κ = κ :=
    MonoidHom.ext fun _ => one_mul _
  simp only [hone, MonoidHom.one_apply, Units.val_one, hsplit, hG, hH] at horth
  change (∑ κ : D, artinConductor R G (characterRepresentation κ.val)) = _
  apply (Rat.cast_injective (α := ℂ))
  push_cast
  simp only [rankOne_artinConductor_eq_classSum R _ b hb, ← Finset.mul_sum]
  change (Nat.card (lowerGroup R G 0) : ℂ)⁻¹ *
    (∑ κ : D, ∑ g : G, w g * (1 - (κ.val g : ℂ))) = _
  rw [horth, Finset.sum_sub_distrib]
  ring

end ArtinConductor

end Langlands.Ramification
