import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.GroupTheory.Index

/-! # Finite quotient pairings and the relative index of a sum and an intersection -/

noncomputable section

namespace Langlands.BushnellKutzko

universe u uX uY

section Indices

variable {A : Type u} [AddCommGroup A]

/-- The indices of a sum and an intersection multiply to the product of the two
original indices. The natural-valued index convention applies, including zero
for an infinite quotient. -/
theorem relIndex_inf_mul_sup (H H' J J' : AddSubgroup A) (h : H ≤ J) (h' : H' ≤ J') :
    (H ⊓ H').relIndex (J ⊓ J') * (H ⊔ H').relIndex (J ⊔ J') =
      H.relIndex J * H'.relIndex J' := by
  let f : J × J' →+ A := J.subtype.coprod J'.subtype
  let k : (J ⊓ J' : AddSubgroup A) →+ J × J' :=
    (AddSubgroup.inclusion inf_le_left).prod (-(AddSubgroup.inclusion inf_le_right))
  let S : AddSubgroup (J × J') := (H.addSubgroupOf J).prod (H'.addSubgroupOf J')
  have hf : f.range = J ⊔ J' := by
    ext x
    constructor
    · rintro ⟨⟨z, w⟩, rfl⟩
      exact AddSubgroup.add_mem_sup z.property w.property
    · rintro (hx : x ∈ J ⊔ J')
      obtain ⟨z, hz, w, hw, rfl⟩ := AddSubgroup.mem_sup.mp hx
      exact ⟨(⟨z, hz⟩, ⟨w, hw⟩), rfl⟩
  have hS : S.map f = H ⊔ H' := by
    ext x
    constructor
    · rintro ⟨⟨z, w⟩, hz, rfl⟩
      exact AddSubgroup.add_mem_sup hz.1 hz.2
    · rintro (hx : x ∈ H ⊔ H')
      obtain ⟨z, hz, w, hw, rfl⟩ := AddSubgroup.mem_sup.mp hx
      exact ⟨(⟨z, h hz⟩, ⟨w, h' hw⟩), ⟨hz, hw⟩, rfl⟩
  have hk : k.range = f.ker := by
    ext x
    rcases x with ⟨z, w⟩
    constructor
    · rintro ⟨v, hv⟩
      rw [← hv]
      change (v : A) + -(v : A) = 0
      exact add_neg_cancel _
    · intro hx
      have hz : (z : A) + (w : A) = 0 := hx
      have hw : -(z : A) = (w : A) := neg_eq_of_add_eq_zero_right hz
      have hzw : (z : A) ∈ J' := by
        rw [← neg_neg (z : A), hw]
        exact J'.neg_mem w.property
      refine ⟨⟨z, z.property, hzw⟩, Prod.ext (Subtype.ext rfl) (Subtype.ext hw)⟩
  have hcomp : S.comap k = (H ⊓ H').addSubgroupOf (J ⊓ J') := by
    ext x
    change ((x : A) ∈ H ∧ -(x : A) ∈ H') ↔ ((x : A) ∈ H ∧ (x : A) ∈ H')
    rw [H'.neg_mem_iff]
  have hunion : (H ⊔ H').relIndex (J ⊔ J') = (S ⊔ f.ker).index := by
    rw [← hS, ← hf, ← AddSubgroup.map_top, AddSubgroup.relIndex_map_map,
      top_sup_eq, AddSubgroup.relIndex_top_right]
  have hinter : (H ⊓ H').relIndex (J ⊓ J') = S.relIndex (S ⊔ f.ker) := by
    rw [AddSubgroup.relIndex_sup_left, ← hk, ← AddSubgroup.index_comap, hcomp]
    rfl
  rw [hunion, hinter, AddSubgroup.relIndex_mul_index le_sup_left]
  exact AddSubgroup.index_prod _ _

end Indices

section Pairing

variable {X : Type uX} [AddCommGroup X] {Y : Type uY} [AddCommGroup Y]
  (U : AddSubgroup X) (V : AddSubgroup Y) (b : X →+ AddChar Y ℂ)
  (hU : ∀ x ∈ U, b x = 0) (hV : ∀ x y, y ∈ V → b x y = 1)

/-- A character pairing which kills two subgroups descends to the two quotients. -/
def quotientCharacterPairing : (X ⧸ U) →+ AddChar (Y ⧸ V) ℂ := by
  let χ : X →+ AddChar (Y ⧸ V) ℂ :=
    { toFun x := AddChar.toAddMonoidHomEquiv.symm
        (QuotientAddGroup.lift V (b x).toAddMonoidHom (hV x))
      map_zero' := by
        ext q : 1
        obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective V q
        change b 0 y = 1
        rw [map_zero]
        rfl
      map_add' x z := by
        ext q : 1
        obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective V q
        change b (x + z) y = b x y * b z y
        rw [map_add]
        rfl }
  exact QuotientAddGroup.lift U χ fun x hx => by
    ext q : 1
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective V q
    change b x y = 1
    rw [hU x hx]
    rfl

@[simp] theorem quotientCharacterPairing_mk (x : X) (y : Y) :
    quotientCharacterPairing U V b hU hV (QuotientAddGroup.mk' U x) (QuotientAddGroup.mk' V y) =
      b x y := rfl

include hU hV in
/-- If the left radical is the specified denominator and the right quotient is
finite, the left quotient has at most the cardinality of the right quotient. -/
theorem index_le_of_quotientCharacterPairing [V.FiniteIndex]
    (hker : ∀ x, (∀ y, b x y = 1) → x ∈ U) : U.index ≤ V.index := by
  let f := quotientCharacterPairing U V b hU hV
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective U x
    apply (QuotientAddGroup.eq_zero_iff z).mpr
    apply hker
    intro y
    exact congrArg (fun χ : AddChar (Y ⧸ V) ℂ => χ (QuotientAddGroup.mk' V y)) hx
  let := Fintype.ofFinite (Y ⧸ V)
  have hcard : Nat.card (AddChar (Y ⧸ V) ℂ) = V.index := by
    change Nat.card (AddChar (Y ⧸ V) ℂ) = Nat.card (Y ⧸ V)
    simp only [Nat.card_eq_fintype_card, AddChar.card_eq]
  rw [← hcard]
  exact Nat.card_le_card_of_injective _ hf

end Pairing

end Langlands.BushnellKutzko
