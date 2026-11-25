/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Pi.Basic

/-! # Joint essential surjectivity from individual lifts and idempotent splitting

Source: the retract argument for finite product decompositions of module categories.
(blueprint: lem-dl-a1-joint-essential-surjectivity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe uC vC uD vD uI
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private theorem essImage_of_retract_of_fullyFaithful
    {C : Type uC} [Category.{vC} C] [IsIdempotentComplete C]
    {D : Type uD} [Category.{vD} D] (F : C ⥤ D) [F.Full] [F.Faithful]
    {X : D} {Z : C} (s : Retract X (F.obj Z)) : F.essImage X := by
  let p : Z ⟶ Z := F.preimage (s.r ≫ s.i)
  have hp : F.map p = s.r ≫ s.i := F.map_preimage _
  have hpp : p ≫ p = p := by
    apply F.map_injective
    simp only [F.map_comp, hp, Category.assoc, s.retract_assoc]
  obtain ⟨W, a, b, hab, hba⟩ := IsIdempotentComplete.idempotents_split Z p hpp
  have hmap : F.map b ≫ F.map a = s.r ≫ s.i := by
    rw [← F.map_comp, hba, hp]
  have hsplit : F.map a ≫ F.map b = 𝟙 (F.obj W) := by
    rw [← F.map_comp, hab, F.map_id]
  refine ⟨W, ⟨{
    hom := F.map a ≫ s.r
    inv := s.i ≫ F.map b
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩⟩
  · calc
      (F.map a ≫ s.r) ≫ s.i ≫ F.map b =
          F.map a ≫ (F.map b ≫ F.map a) ≫ F.map b := by
        simp only [Category.assoc, hmap]
      _ = 𝟙 (F.obj W) := by simp [← Category.assoc, hsplit]
  · calc
      (s.i ≫ F.map b) ≫ F.map a ≫ s.r = s.i ≫ (s.r ≫ s.i) ≫ s.r := by
        rw [Category.assoc, ← Category.assoc (F.map b), hmap]
      _ = 𝟙 X := by simp

/-- A jointly fully faithful finite family with individual object lifts lifts every tuple.
Source: finite product decomposition of module categories, the retract argument.
(blueprint: lem-dl-a1-joint-essential-surjectivity).

Proof: lift the ith prescribed object through L_i, and form the finite biproduct
of those lifts. In each target category the prescribed object is a retract of
its image, using the ith inclusion and projection. These coordinate retracts
form a retract of the whole tuple. Full faithfulness lifts its idempotent to
the source category, and splitting it supplies the desired global preimage.
This includes the empty family: its tuple is a retract of the image of zero. -/
theorem joint_essSurj_of_finite_biproducts
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C] [IsIdempotentComplete C]
    {I : Type uI} [Finite I] {D : I → Type uD} [∀ i, Category.{vD} (D i)]
    (L : ∀ i, C ⥤ D i) [∀ i, (L i).EssSurj]
    [(Functor.pi' L).Full] [(Functor.pi' L).Faithful] :
    (Functor.pi' L).EssSurj := by
  classical
  let := Fintype.ofFinite I
  constructor
  intro N
  let M (i : I) := (L i).objPreimage (N i)
  let e (i : I) : (L i).obj (M i) ≅ N i := (L i).objObjPreimageIso (N i)
  apply essImage_of_retract_of_fullyFaithful (Functor.pi' L)
    (Z := ⨁ M)
  refine {
    i := fun i ↦ (e i).inv ≫ (L i).map (biproduct.ι M i)
    r := fun i ↦ (L i).map (biproduct.π M i) ≫ (e i).hom
    retract := ?_ }
  funext i
  dsimp only [Pi.comp_apply, Pi.id_apply]
  rw [Category.assoc, ← Functor.map_comp_assoc, biproduct.ι_π_self, Functor.map_id,
    Category.id_comp, Iso.inv_hom_id]

end CategoryTheory
