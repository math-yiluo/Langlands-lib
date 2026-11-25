/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # The coordinate of a split line inclusion -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem coordinates
    {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
    {A B K : C} (a : A ⟶ K) (b : B ⟶ K) [IsIso (biprod.desc a b)]
    (t : K ⟶ B) (ha : a ≫ t = 0) (hb : b ≫ t = 𝟙 B)
    {W : C} (k : W ⟶ K) :
    k = (k ≫ inv (biprod.desc a b) ≫ biprod.fst) ≫ a + (k ≫ t) ≫ b := by
  have ht : inv (biprod.desc a b) ≫ biprod.snd = t := by
    apply (cancel_epi (biprod.desc a b)).mp
    simp only [IsIso.hom_inv_id_assoc]
    apply biprod.hom_ext'
    · simpa only [biprod.inl_snd, biprod.inl_desc_assoc] using ha.symm
    · simpa only [biprod.inr_snd, biprod.inr_desc_assoc] using hb.symm
  rw [← ht]
  calc
    _ = k ≫ inv (biprod.desc a b) ≫ biprod.desc a b := by
      simp only [IsIso.inv_hom_id, Category.comp_id]
    _ = _ := by
      simpa only [Preadditive.comp_add, Category.assoc] using
        congrArg (fun z ↦ k ≫ inv (biprod.desc a b) ≫ z)
          (biprod.desc_eq (f := a) (g := b))

/-- A split inclusion killed by a split projection has invertible complementary
coordinate when split endomorphisms of that complementary line are invertible.

Source: the unit entry in the unit/Chern splitting, diagonal coefficients (3)
(blueprint: lem-diagonal-split-line-coordinate).

Proof: expand the map into its two coordinates in the biproduct decomposition.
Its second coordinate vanishes by the projection equation, so it factors through
the first inclusion. Composing a retraction of the map with that inclusion gives
a retraction of its first coordinate. Conjugate by the specified line isomorphism
to obtain a split endomorphism; the assumed rank-one property makes it invertible.
Cancel the line isomorphism to conclude. -/
theorem splitLineCoordinate_isIso
    {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
    {A A' B K : C} (a : A' ⟶ K) (b : B ⟶ K) [IsIso (biprod.desc a b)]
    (t : K ⟶ B) (ha : a ≫ t = 0) (hb : b ≫ t = 𝟙 B)
    (k : A ⟶ K) [IsSplitMono k] (hk : k ≫ t = 0) (i : A ≅ A')
    (hline : ∀ q : End A', IsSplitMono (q).asHom → IsIso (q).asHom) :
    IsIso (k ≫ inv (biprod.desc a b) ≫ biprod.fst) := by
  let d := k ≫ inv (biprod.desc a b) ≫ biprod.fst
  have hd : k = d ≫ a := by
    simpa only [hk, zero_comp, add_zero, d] using coordinates a b t ha hb k
  have : IsSplitMono d := ⟨⟨a ≫ retraction k, by
    rw [← Category.assoc, ← hd, IsSplitMono.id]⟩⟩
  have : IsSplitMono (i.inv ≫ d) := inferInstance
  have : IsIso (i.inv ≫ d) := hline _ inferInstance
  exact IsIso.of_isIso_comp_left i.inv d

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
