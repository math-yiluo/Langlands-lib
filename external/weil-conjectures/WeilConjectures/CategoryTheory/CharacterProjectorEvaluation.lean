/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Tactic.LinearCombination

/-! # Evaluation on the image of a character projector

The finite-product calculation in the splitting chart of an Artin–Schreier torsor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u w t

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- If a finite product is acted on by translations of its index group, the image of
its normalized character projector is identified with a single factor by evaluation at zero.

Source: latest blueprint, `prop-kernel-lisse.proof.md`, splitting-chart calculation
(blueprint: lem-kernel-character-projector-evaluation).

Proof. Write `q` for the order of the group. The map from one factor to the product with
components `χ(a)` is `j`. The map `r` in the other direction is the normalized weighted
sum of projections with weights `χ(-a)`. Character cancellation gives `j ≫ r = 1`.
Reindexing by translation gives `e = r ≫ j`, and evaluation at zero satisfies
`j ≫ ρ(0) = 1`. Thus the maps `image(e) → N` and `N → image(e)` obtained from evaluation
and `j` are inverse, as can be checked after the monomorphism `image.ι e` and the
epimorphism `factorThruImage e`. This works for the trivial character and zero objects. -/
theorem characterProjector_evaluation_isIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : Type w} [CommRing K] [Linear K C]
    {G : Type t} [AddCommGroup G] [Fintype G] [Invertible (Fintype.card G : K)]
    {P N : C} [HasProduct (fun _ : G ↦ N)]
    (ρ : G → (P ⟶ N)) [IsIso (Pi.lift ρ)]
    (τ : G → (P ⟶ P)) (hτ : ∀ a c, τ c ≫ ρ a = ρ (a + c))
    (χ : AddChar G K) :
    IsIso (image.ι (∑ c : G, (⅟(Fintype.card G : K) * χ (-c)) • τ c) ≫ ρ 0) := by
  classical
  let e := ∑ c : G, (⅟(Fintype.card G : K) * χ (-c)) • τ c
  let j : N ⟶ P := Pi.lift (fun a : G ↦ χ a • 𝟙 N) ≫ inv (Pi.lift ρ)
  let r : P ⟶ N := ∑ c : G, (⅟(Fintype.card G : K) * χ (-c)) • ρ c
  have hj (a : G) : j ≫ ρ a = χ a • 𝟙 N := by
    have hπ : inv (Pi.lift ρ) ≫ ρ a = Pi.π (fun _ : G ↦ N) a := by
      rw [IsIso.inv_comp_eq, Pi.lift_comp_π]
    simp only [j, Category.assoc, hπ, Pi.lift_comp_π]
  have hjr : j ≫ r = 𝟙 N := by
    simp only [r, Preadditive.comp_sum, Linear.comp_smul, hj, smul_smul,
      mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
      mul_one, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K,
      smul_smul, mul_invOf_self, one_smul]
  have he : e = r ≫ j := by
    apply (cancel_mono (Pi.lift ρ)).1
    apply Pi.hom_ext
    intro a
    simp only [Category.assoc, Pi.lift_comp_π, e, Preadditive.sum_comp,
      Linear.smul_comp, hτ, hj, Linear.comp_smul, Category.comp_id, r,
      smul_smul]
    refine Fintype.sum_equiv (Equiv.addLeft a) _ _ fun c ↦ ?_
    simp only [Equiv.coe_addLeft, neg_add_rev, AddChar.map_add_eq_mul]
    congr 1
    have h : χ a * χ (-a) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination -(⅟(Fintype.card G : K) * χ (-c)) * h
  have hj₀ : j ≫ ρ 0 = 𝟙 N := by simpa using hj 0
  let f : image e ⟶ N := image.ι e ≫ ρ 0
  let g : N ⟶ image e := j ≫ factorThruImage e
  have hfg : f ≫ g = 𝟙 _ := by
    apply (cancel_mono (image.ι e)).1
    apply (cancel_epi (factorThruImage e)).1
    simp only [f, g, Category.assoc, image.fac_assoc, image.fac, Category.id_comp]
    rw [he]
    simp only [Category.assoc, reassoc_of% hj₀, reassoc_of% hjr]
  have hgf : g ≫ f = 𝟙 _ := by
    simp only [g, f, Category.assoc, image.fac_assoc]
    rw [he]
    simp only [Category.assoc, reassoc_of% hjr, hj₀]
  exact ⟨⟨g, hfg, hgf⟩⟩

/-- Evaluation on a character image can use any finite enumeration of the product chart.

Source: the splitting-chart character calculation, with its factors enumerated by Fin n
(blueprint: lem-kernel-character-projector-evaluation).

Proof. The product over the group is obtained from the enumerated product by the
reindexing isomorphism. Compare their projections to identify the two product maps.
The group-indexed product map is therefore invertible, and the character-image
evaluation theorem applies. All reindexing takes place in the abstract category. -/
theorem characterProjector_reindexed_evaluation_isIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : Type w} [CommRing K] [Linear K C]
    {G : Type t} [AddCommGroup G] [Fintype G] [Invertible (Fintype.card G : K)]
    {P N : C} [HasProduct (fun _ : G ↦ N)]
    (ρ : G → (P ⟶ N)) (n : ℕ) (ε : Fin n ≃ G)
    [HasProduct (fun _ : Fin n ↦ N)] (hρ : IsIso (Pi.lift (fun j ↦ ρ (ε j))))
    (τ : G → (P ⟶ P)) (hτ : ∀ a c, τ c ≫ ρ a = ρ (a + c))
    (χ : AddChar G K) :
    IsIso (image.ι (∑ c : G, (⅟(Fintype.card G : K) * χ (-c)) • τ c) ≫ ρ 0) := by
  have := hρ
  have he : Pi.lift ρ = Pi.lift (fun j ↦ ρ (ε j)) ≫
      (Pi.reindex ε (fun _ : G ↦ N)).hom := by
    apply Pi.hom_ext
    intro a
    obtain ⟨j, rfl⟩ := ε.surjective a
    rw [Category.assoc, Pi.reindex_hom_π, Pi.lift_comp_π]
    exact (Pi.lift_comp_π (fun j ↦ ρ (ε j)) j).symm
  have : IsIso (Pi.lift ρ) := by rw [he]; infer_instance
  exact characterProjector_evaluation_isIso ρ τ hτ χ

end CategoryTheory
