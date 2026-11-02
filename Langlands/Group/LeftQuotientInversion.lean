import Langlands.Group.LeftQuotient

/-! # Inversion between the two canonical coset topologies -/

noncomputable section

namespace Langlands.Induction

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

section Inversion

variable [ContinuousInv G]

/-- Inversion descends to a homeomorphism from `P * g` classes to `g * P` classes. -/
def quotientInversion (P : Subgroup G) : LeftQuotient P ≃ₜ G ⧸ P :=
  Homeomorph.Quotient.congr (Homeomorph.inv G) (by
    intro x y
    simp only [QuotientGroup.rightRel_apply, QuotientGroup.leftRel_apply,
      Homeomorph.coe_inv, inv_inv]
    constructor <;> intro h <;> simpa only [mul_inv_rev, inv_inv] using P.inv_mem h)

@[simp] theorem quotientInversion_mk (P : Subgroup G) (g : G) :
    quotientInversion P (quotientMap P g) = (QuotientGroup.mk g⁻¹ : G ⧸ P) := rfl

@[simp] theorem quotientInversion_symm_mk (P : Subgroup G) (g : G) :
    (quotientInversion P).symm (QuotientGroup.mk g : G ⧸ P) = quotientMap P g⁻¹ := rfl

/-- The two quotient conventions have equivalent compactness assertions. -/
theorem compactSpace_leftQuotient_iff (P : Subgroup G) :
    CompactSpace (LeftQuotient P) ↔ CompactSpace (G ⧸ P) := by
  constructor
  · intro h
    let := h
    exact (quotientInversion P).compactSpace
  · intro h
    let := h
    exact (quotientInversion P).symm.compactSpace

end Inversion

/-- A compact set meeting every `g * P` class makes that quotient compact. -/
theorem compactSpace_quotient_of_compact_representatives (P : Subgroup G)
    {C : Set G} (hC : IsCompact C)
    (hcover : ∀ g : G, ∃ c ∈ C, ∃ p ∈ P, g = c * p) :
    CompactSpace (G ⧸ P) := by
  rw [← isCompact_univ_iff]
  have himage : (QuotientGroup.mk : G → G ⧸ P) '' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨c, hc, p, hp, rfl⟩ := hcover g
      refine ⟨c, hc, Quotient.sound ?_⟩
      change QuotientGroup.leftRel P c (c * p)
      rw [QuotientGroup.leftRel_apply]
      simpa only [inv_mul_cancel_left] using hp
  rw [← himage]
  exact hC.image continuous_quot_mk

/-- A compact set meeting every `P * g` class makes that quotient compact. -/
theorem compactSpace_leftQuotient_of_compact_representatives (P : Subgroup G)
    {C : Set G} (hC : IsCompact C)
    (hcover : ∀ g : G, ∃ p ∈ P, ∃ c ∈ C, g = p * c) :
    CompactSpace (LeftQuotient P) := by
  rw [← isCompact_univ_iff]
  have himage : quotientMap P '' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨p, hp, c, hc, rfl⟩ := hcover g
      refine ⟨c, hc, Quotient.sound ?_⟩
      change QuotientGroup.rightRel P c (p * c)
      rw [QuotientGroup.rightRel_apply]
      simpa only [mul_inv_cancel_right] using hp
  rw [← himage]
  exact hC.image continuous_quot_mk

end Langlands.Induction
