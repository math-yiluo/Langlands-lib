/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Representative comparison for derived adjunction mates

Source: Stacks 0FND and 09T5.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a av b bv c cv d dv a' av' b' bv' c' cv' d' dv'
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
  {AD : Type a'} [Category.{av'} AD] {BD : Type b'} [Category.{bv'} BD]
  {CD : Type c'} [Category.{cv'} CD] {DD : Type d'} [Category.{dv'} DD]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {LD₁ : AD ⥤ BD} {RD₁ : BD ⥤ AD} {LD₂ : CD ⥤ DD} {RD₂ : DD ⥤ CD}
  {G : A ⥤ C} {H : B ⥤ D} {GD : AD ⥤ CD} {HD : BD ⥤ DD}
  {QA : A ⥤ AD} {QB : B ⥤ BD} {QC : C ⥤ CD} {QD : D ⥤ DD}

/-- A derived mate is computed by the ordinary mate and the normalized derived
comparisons. Source: Stacks 0FND and 09T5
(blueprint: lem-pur-derived-mate-comparison).
Proof: apply the second derived Hom bijection and postcompose with the invertible
right factorization. The mate transpose identity moves the first comparison through
the first adjunction. Its normalization, the right-square comparison, and naturality
of the G factorization reduce that side to the ordinary unit followed by the ordinary
square. The ordinary mate identity identifies this with the second ordinary transpose.
The second normalization gives the other side, and both cancellations are injective. -/
theorem derivedMate_comparison
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (ad₁ : LD₁ ⊣ RD₁) (ad₂ : LD₂ ⊣ RD₂)
    (ε₁ : QA ⋙ LD₁ ⟶ L₁ ⋙ QB) (ε₂ : QC ⋙ LD₂ ⟶ L₂ ⋙ QD)
    (ρ₁ : QB ⋙ RD₁ ≅ R₁ ⋙ QA) (ρ₂ : QD ⋙ RD₂ ≅ R₂ ⋙ QC)
    (γ : QA ⋙ GD ≅ G ⋙ QC) (η : QB ⋙ HD ≅ H ⋙ QD)
    (h₁ : ∀ P K (f : L₁.obj P ⟶ K),
      ad₁.homEquiv _ _ (ε₁.app P ≫ QB.map f) =
        QA.map (a₁.homEquiv _ _ f) ≫ ρ₁.inv.app K)
    (h₂ : ∀ P K (f : L₂.obj P ⟶ K),
      ad₂.homEquiv _ _ (ε₂.app P ≫ QD.map f) =
        QC.map (a₂.homEquiv _ _ f) ≫ ρ₂.inv.app K)
    (τ : TwoSquare R₁ H G R₂) (τD : TwoSquare RD₁ HD GD RD₂)
    (hτ : ∀ K,
      τD.app (QB.obj K) ≫ RD₂.map (η.hom.app K) ≫ ρ₂.hom.app (H.obj K) =
        GD.map (ρ₁.hom.app K) ≫ γ.hom.app (R₁.obj K) ≫ QC.map (τ.app K))
    (ι : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (hι : ∀ P, a₂.homEquiv _ _ (ι.app P) = G.map (a₁.unit.app P) ≫ τ.app (L₁.obj P))
    (P : A) :
    ((mateEquiv ad₁ ad₂).symm τD).app (QA.obj P) ≫
        HD.map (ε₁.app P) ≫ η.hom.app (L₁.obj P) =
      LD₂.map (γ.hom.app P) ≫ ε₂.app (G.obj P) ≫ QD.map (ι.app P) := by
  apply (ad₂.homEquiv _ _).injective
  apply (cancel_mono (ρ₂.hom.app (H.obj (L₁.obj P)))).1
  rw [← Category.assoc, ad₂.homEquiv_naturality_right, adjunctionMate_transpose]
  have he : ad₁.homEquiv _ _ (ε₁.app P) =
      QA.map (a₁.unit.app P) ≫ ρ₁.inv.app (L₁.obj P) := by
    have h := h₁ P (L₁.obj P) (𝟙 _)
    erw [QB.map_id, Category.comp_id, a₁.homEquiv_unit,
      R₁.map_id, Category.comp_id] at h
    exact h
  rw [he, GD.map_comp]
  simp only [Category.assoc]
  erw [hτ]
  rw [← Category.assoc (GD.map (ρ₁.inv.app (L₁.obj P)))
    (GD.map (ρ₁.hom.app (L₁.obj P))), ← GD.map_comp, ρ₁.inv_hom_id_app,
    GD.map_id, Category.id_comp]
  change GD.map (QA.map (a₁.unit.app P)) ≫
    γ.hom.app (R₁.obj (L₁.obj P)) ≫ QC.map (τ.app (L₁.obj P)) = _
  rw [← Functor.comp_map]
  erw [γ.hom.naturality_assoc]
  rw [ad₂.homEquiv_naturality_left]
  erw [h₂]
  simp only [Category.assoc, ρ₂.inv_hom_id_app]
  erw [hι, QC.map_comp, Category.comp_id]
  rfl

end CategoryTheory
