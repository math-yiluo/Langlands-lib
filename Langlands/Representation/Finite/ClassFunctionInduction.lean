/-
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Adapted from the Anthropic Lean formalization of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, file `Definitions/Def_ClassFunction_Induced.lean`.
Changes: the declarations are renamed into `Langlands.FiniteRep` (`ClassFunction.induced` becomes
`inducedClassFunction`, its lemmas follow); Mathlib is imported by module and no option is
set; `inducedClassFunction_conj` ends with `rfl`; deprecated lemma names are replaced. The paired
Markdown file lists the changes.
-/
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group

/-!
# Induction of class functions

For a finite group `G`, a subgroup `H` and a function `φ : G → K` with values in a field,
`inducedClassFunction H φ` is the normalized induced function
`g ↦ |H|⁻¹ * ∑ x : G, [x⁻¹ g x ∈ H] φ (x⁻¹ g x)` (Serre, *Linear Representations of Finite Groups*,
§7.2). Only the values of `φ` on `H` matter. The file proves conjugation invariance, linearity,
the projection formula against a conjugation-invariant function, induction from `⊤`, and induction
in stages.

This is an operation on functions: it does not construct an induced representation. The Library's
actual induction is `Langlands.FiniteRep.induceRep`; `InducedCharacterProof` computes its character
by the same formula.
-/

noncomputable section

namespace Langlands.FiniteRep

variable {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]

open scoped Classical in
/-- The normalized induction of a function `φ : G → K` from a subgroup `H`:
`g ↦ |H|⁻¹ * ∑ x : G, [x⁻¹ g x ∈ H] φ (x⁻¹ g x)`. -/
def inducedClassFunction (H : Subgroup G) (φ : G → K) : G → K :=
  fun g => (Nat.card H : K)⁻¹ * ∑ x : G, if x⁻¹ * g * x ∈ H then φ (x⁻¹ * g * x) else 0

theorem inducedClassFunction_apply (H : Subgroup G) [DecidablePred (· ∈ H)] (φ : G → K) (g : G) :
    inducedClassFunction H φ g =
      (Nat.card H : K)⁻¹ * ∑ x : G, if x⁻¹ * g * x ∈ H then φ (x⁻¹ * g * x) else 0 := by
  unfold inducedClassFunction
  congr 1
  exact Finset.sum_congr rfl fun x _ => by congr

theorem inducedClassFunction_congr (H : Subgroup G) {φ ψ : G → K} (h : ∀ x ∈ H, φ x = ψ x) :
    inducedClassFunction H φ = inducedClassFunction H ψ := by
  classical
  funext g
  rw [inducedClassFunction_apply, inducedClassFunction_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · exact h _ hx
  · rfl

theorem inducedClassFunction_conj (H : Subgroup G) (φ : G → K) (y g : G) :
    inducedClassFunction H φ (y⁻¹ * g * y) = inducedClassFunction H φ g := by
  classical
  rw [inducedClassFunction_apply, inducedClassFunction_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_
  have : x⁻¹ * (y⁻¹ * g * y) * x = (y * x)⁻¹ * g * (y * x) := by group
  simp only [Equiv.coe_mulLeft, this]
  rfl

theorem inducedClassFunction_add (H : Subgroup G) (φ ψ : G → K) :
    inducedClassFunction H (φ + ψ) = inducedClassFunction H φ + inducedClassFunction H ψ := by
  classical
  funext g
  simp only [Pi.add_apply, inducedClassFunction_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem inducedClassFunction_zero (H : Subgroup G) : inducedClassFunction H (0 : G → K) = 0 := by
  classical
  funext g
  rw [inducedClassFunction_apply, Pi.zero_apply]
  simp only [Pi.zero_apply, ite_self, Finset.sum_const_zero, mul_zero]

theorem inducedClassFunction_const_mul (H : Subgroup G) (c : K) (φ : G → K) :
    inducedClassFunction H (fun x => c * φ x) = fun g => c * inducedClassFunction H φ g := by
  classical
  funext g
  simp only [inducedClassFunction_apply]
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem inducedClassFunction_sum {ι : Type*} (H : Subgroup G) (s : Finset ι) (φ : ι → G → K) :
    inducedClassFunction H (fun x => ∑ i ∈ s, φ i x) =
      fun g => ∑ i ∈ s, inducedClassFunction H (φ i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact inducedClassFunction_zero H
  | insert i s hi ih =>
    funext g
    simp only [Finset.sum_insert hi]
    have : (fun x => φ i x + ∑ j ∈ s, φ j x) = φ i + fun x => ∑ j ∈ s, φ j x := by
      funext x; simp
    rw [this, inducedClassFunction_add, Pi.add_apply, ih]

theorem inducedClassFunction_mul_of_conj_invariant (H : Subgroup G) (φ f : G → K)
    (hf : ∀ x g : G, f (x⁻¹ * g * x) = f g) (g : G) :
    inducedClassFunction H φ g * f g = inducedClassFunction H (fun y => φ y * f y) g := by
  classical
  simp only [inducedClassFunction_apply]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [hf]
  · simp

theorem inducedClassFunction_top_of_conj_invariant [CharZero K] (φ : G → K)
    (hφ : ∀ x g : G, φ (x⁻¹ * g * x) = φ g) : inducedClassFunction (⊤ : Subgroup G) φ = φ := by
  classical
  funext g
  rw [inducedClassFunction_apply, Subgroup.card_top, Nat.card_eq_fintype_card]
  simp only [Subgroup.mem_top, ite_true, hφ, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [← mul_assoc]
  have hG : (Fintype.card G : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hG, one_mul]

/-- Induction in stages: inducing from `H` the extension by zero of `inducedClassFunction L ψ`,
for a subgroup `L` of `H`, is inducing from the image of `L` in `G` the extension by zero of
`ψ`. -/
theorem inducedClassFunction_inducedClassFunction [CharZero K] (H : Subgroup G) [Fintype H]
    [DecidablePred (· ∈ H)] (L : Subgroup H) (ψ : H → K) :
    inducedClassFunction H (fun g => if hg : g ∈ H then inducedClassFunction L ψ ⟨g, hg⟩ else 0) =
      inducedClassFunction (L.map H.subtype) (fun g => if hg : g ∈ H then ψ ⟨g, hg⟩ else 0) := by
  classical
  funext g
  rw [inducedClassFunction_apply, inducedClassFunction_apply]

  set ψ' : G → K := fun g => if hg : g ∈ H then ψ ⟨g, hg⟩ else 0 with hψ'
  set L' : Subgroup G := L.map H.subtype with hL'
  have hLcard : (Nat.card L' : K) = Nat.card L := by
    congr 1
    exact Nat.card_congr (L.equivMapOfInjective H.subtype H.subtype_injective).toEquiv.symm
  have hmemL : ∀ y : G, y ∈ L' ↔ ∃ hy : y ∈ H, (⟨y, hy⟩ : H) ∈ L := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, by simpa using hz⟩
    · rintro ⟨hy, hL⟩
      exact ⟨⟨y, hy⟩, hL, rfl⟩
  have hL'H : L' ≤ H := by
    intro y hy
    rw [hmemL] at hy
    exact hy.1

  set F : G → K := fun z => if z⁻¹ * g * z ∈ L' then ψ' (z⁻¹ * g * z) else 0 with hF
  have hH0 : (Nat.card H : K) ≠ 0 := by
    have : 0 < Nat.card H := Nat.card_pos
    exact_mod_cast this.ne'

  have hinner : ∀ x : G,
      (if x⁻¹ * g * x ∈ H then
        (if hx : x⁻¹ * g * x ∈ H then inducedClassFunction L ψ ⟨x⁻¹ * g * x, hx⟩ else 0)
        else 0) =
      (Nat.card L : K)⁻¹ * ∑ y : G, if y ∈ H then F (x * y) else 0 := by
    intro x
    by_cases hx : x⁻¹ * g * x ∈ H
    · rw [ite_eq_left hx, dite_eq_left hx, inducedClassFunction_apply]
      congr 1
      have key : ∀ y : H, (if y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y ∈ L then
          ψ (y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y) else 0) = F (x * y) := by
        intro y
        have hcoe : (x * y)⁻¹ * g * (x * y) = ((y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y : H) : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        have hmemL' : ∀ w : H, (w : G) ∈ L' ↔ w ∈ L := by
          intro w
          rw [hmemL]
          exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨w.2, h⟩⟩
        rw [hF]
        dsimp only
        rw [hcoe, hmemL']
        split_ifs with hw
        · rw [hψ']
          beta_reduce
          split_ifs with h'
          · rfl
          · exact absurd (Subtype.coe_prop _) h'
        · rfl
      rw [Finset.sum_congr rfl (fun y _ => key y)]

      rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ H)) (by simp) (fun y => F (x * y)),
        Finset.sum_filter]
    · rw [ite_eq_right hx]
      symm
      rw [mul_eq_zero]
      right
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [ite_eq_right_iff]
      intro hy
      rw [hF]
      dsimp only
      rw [ite_eq_right]
      intro hyL
      apply hx
      have hmem : (x * y)⁻¹ * g * (x * y) ∈ H := hL'H hyL
      have : x⁻¹ * g * x = y * ((x * y)⁻¹ * g * (x * y)) * y⁻¹ := by group
      rw [this]
      exact H.mul_mem (H.mul_mem hy hmem) (H.inv_mem hy)

  have hswap : ∑ x : G, (Nat.card L : K)⁻¹ * ∑ y : G, (if y ∈ H then F (x * y) else 0) =
      (Nat.card L : K)⁻¹ * ((Nat.card H : K) * ∑ z : G, F z) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    have : ∀ y : G, ∑ x : G, (if y ∈ H then F (x * y) else 0) =
        if y ∈ H then ∑ z : G, F z else 0 := by
      intro y
      split_ifs with hy
      · exact Fintype.sum_equiv (Equiv.mulRight y) _ _ fun x => rfl
      · simp
    simp_rw [this]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have : (Finset.univ.filter (· ∈ H)).card = Nat.card H := by
      rw [← Fintype.card_subtype]
      convert (Nat.card_eq_fintype_card (α := H)).symm
    exact_mod_cast this
  have hL0 : (Nat.card L : K) ≠ 0 := by
    have : 0 < Nat.card L := Nat.card_pos
    exact_mod_cast this.ne'
  simp_rw [hinner]
  rw [hswap, hLcard]
  field_simp

end Langlands.FiniteRep

end

