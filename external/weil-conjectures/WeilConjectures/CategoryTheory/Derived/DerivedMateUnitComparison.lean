/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Mates normalized by arbitrary right-derived units

Source: Stacks 0FND and 09T5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory

/-- A mate comparison needs normalization by right-derived units, which need not be
isomorphisms. Source: Zheng Construction 4.1; Stacks 0FND and 09T5.
Proof: transpose the proposed equality through the second derived adjunction.
The mate-transpose formula and naturality move the first left comparison and the
vertical target comparison out of that transpose. Substitute the first normalized
unit formula. The right-square unit equation then replaces the middle three maps.
Naturality of the source vertical comparison moves the ordinary unit to the other
side. The ordinary mate equation and the second normalized Hom formula identify
this with the transpose of the second path. Injectivity of the Hom equivalence
proves equality. No cancellation or invertibility of a right-derived unit is used.
(blueprint: lem-pur-derived-mate-unit-comparison). -/
private theorem unitComparison_aux
    {A B C D AD BD CD DD : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category AD] [Category BD] [Category CD] [Category DD]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {LD₁ : AD ⥤ BD} {RD₁ : BD ⥤ AD} {LD₂ : CD ⥤ DD} {RD₂ : DD ⥤ CD}
    {G : A ⥤ C} {H : B ⥤ D} {GD : AD ⥤ CD} {HD : BD ⥤ DD}
    {QA : A ⥤ AD} {QB : B ⥤ BD} {QC : C ⥤ CD} {QD : D ⥤ DD}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (ad₁ : LD₁ ⊣ RD₁) (ad₂ : LD₂ ⊣ RD₂)
    (ε₁ : QA ⋙ LD₁ ⟶ L₁ ⋙ QB) (ε₂ : QC ⋙ LD₂ ⟶ L₂ ⋙ QD)
    (ρ₁ : R₁ ⋙ QA ⟶ QB ⋙ RD₁) (ρ₂ : R₂ ⋙ QC ⟶ QD ⋙ RD₂)
    (γ : QA ⋙ GD ≅ G ⋙ QC) (η : QB ⋙ HD ≅ H ⋙ QD)
    (h₁ : ∀ P K (f : L₁.obj P ⟶ K),
      ad₁.homEquiv _ _ (ε₁.app P ≫ QB.map f) =
        QA.map (a₁.homEquiv _ _ f) ≫ ρ₁.app K)
    (h₂ : ∀ P K (f : L₂.obj P ⟶ K),
      ad₂.homEquiv _ _ (ε₂.app P ≫ QD.map f) =
        QC.map (a₂.homEquiv _ _ f) ≫ ρ₂.app K)
    (τ : TwoSquare R₁ H G R₂) (τD : TwoSquare RD₁ HD GD RD₂)
    (hτ : ∀ K,
      GD.map (ρ₁.app K) ≫ τD.app (QB.obj K) ≫ RD₂.map (η.hom.app K) =
        γ.hom.app (R₁.obj K) ≫ QC.map (τ.app K) ≫ ρ₂.app (H.obj K))
    (ι : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (hι : ∀ P, a₂.homEquiv _ _ (ι.app P) = G.map (a₁.unit.app P) ≫ τ.app (L₁.obj P))
    (P : A) :
    ((mateEquiv ad₁ ad₂).symm τD).app (QA.obj P) ≫
        HD.map (ε₁.app P) ≫ η.hom.app (L₁.obj P) =
      LD₂.map (γ.hom.app P) ≫ ε₂.app (G.obj P) ≫ QD.map (ι.app P) := by
  apply (ad₂.homEquiv _ _).injective
  rw [← Category.assoc, ad₂.homEquiv_naturality_right, adjunctionMate_transpose]
  have hu := h₁ P _ (𝟙 _)
  erw [QB.map_id, Category.comp_id] at hu
  simp only [Adjunction.homEquiv_id] at hu
  erw [hu, GD.map_comp]
  simp only [Category.assoc]
  erw [hτ]
  rw [← Functor.comp_map]
  erw [γ.hom.naturality_assoc]
  rw [ad₂.homEquiv_naturality_left]
  erw [h₂, hι, QC.map_comp]
  simp only [Functor.id_obj, Functor.comp_map, Category.assoc]

/-- An invertible mate comparison on representatives, normalized by arbitrary
right-derived units. Source: Zheng Construction 4.1 and Lemma 5.16; Stacks 0FND.
Proof: the auxiliary transpose calculation identifies the derived left mate with
its ordinary representative using the two normalized Hom formulas and the right
unit square. The given mate equation identifies that mate with ιD.hom.
Precompose by ιD.inv and postcompose by QD(ι.hom). Cancel the two isomorphism
pairs; the right-derived units are never inverted.
(blueprint: lem-pur-derived-mate-unit-comparison). -/
theorem derivedMate_unitComparison
    {A B C D AD BD CD DD : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category AD] [Category BD] [Category CD] [Category DD]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {LD₁ : AD ⥤ BD} {RD₁ : BD ⥤ AD} {LD₂ : CD ⥤ DD} {RD₂ : DD ⥤ CD}
    {G : A ⥤ C} {H : B ⥤ D} {GD : AD ⥤ CD} {HD : BD ⥤ DD}
    {QA : A ⥤ AD} {QB : B ⥤ BD} {QC : C ⥤ CD} {QD : D ⥤ DD}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (ad₁ : LD₁ ⊣ RD₁) (ad₂ : LD₂ ⊣ RD₂)
    (ε₁ : QA ⋙ LD₁ ⟶ L₁ ⋙ QB) (ε₂ : QC ⋙ LD₂ ⟶ L₂ ⋙ QD)
    (ρ₁ : R₁ ⋙ QA ⟶ QB ⋙ RD₁) (ρ₂ : R₂ ⋙ QC ⟶ QD ⋙ RD₂)
    (γ : QA ⋙ GD ≅ G ⋙ QC) (η : QB ⋙ HD ≅ H ⋙ QD)
    (h₁ : ∀ P K (f : L₁.obj P ⟶ K),
      ad₁.homEquiv _ _ (ε₁.app P ≫ QB.map f) =
        QA.map (a₁.homEquiv _ _ f) ≫ ρ₁.app K)
    (h₂ : ∀ P K (f : L₂.obj P ⟶ K),
      ad₂.homEquiv _ _ (ε₂.app P ≫ QD.map f) =
        QC.map (a₂.homEquiv _ _ f) ≫ ρ₂.app K)
    (τ : TwoSquare R₁ H G R₂) (τD : TwoSquare RD₁ HD GD RD₂)
    (hτ : ∀ K,
      GD.map (ρ₁.app K) ≫ τD.app (QB.obj K) ≫ RD₂.map (η.hom.app K) =
        γ.hom.app (R₁.obj K) ≫ QC.map (τ.app K) ≫ ρ₂.app (H.obj K))
    (ι : L₁ ⋙ H ≅ G ⋙ L₂)
    (hι : ∀ P, a₂.homEquiv _ _ (ι.inv.app P) =
      G.map (a₁.unit.app P) ≫ τ.app (L₁.obj P))
    (ιD : GD ⋙ LD₂ ≅ LD₁ ⋙ HD)
    (hιD : mateEquiv ad₁ ad₂ (TwoSquare.mk _ _ _ _ ιD.hom) = τD)
    (P : A) :
    ιD.inv.app (QA.obj P) ≫ LD₂.map (γ.hom.app P) ≫ ε₂.app (G.obj P) =
      HD.map (ε₁.app P) ≫ η.hom.app (L₁.obj P) ≫ QD.map (ι.hom.app P) := by
  have h := unitComparison_aux a₁ a₂ ad₁ ad₂ ε₁ ε₂ ρ₁ ρ₂ γ η h₁ h₂ τ τD hτ
    ι.inv hι P
  have hm : ((mateEquiv ad₁ ad₂).symm τD) = ιD.hom := by
    have hh := congrArg (fun z ↦ ((mateEquiv ad₁ ad₂).symm z)) hιD
    simpa only [Equiv.symm_apply_apply] using hh.symm
  change ((mateEquiv ad₁ ad₂).symm τD).app (QA.obj P) ≫
    HD.map (ε₁.app P) ≫ η.hom.app (L₁.obj P) = _ at h
  rw [hm] at h
  have hh := congrArg (fun z ↦ ιD.inv.app (QA.obj P) ≫ z ≫ QD.map (ι.hom.app P)) h
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc] at hh
  rw [← QD.map_comp, Iso.inv_hom_id_app] at hh
  erw [QD.map_id, Category.comp_id] at hh
  exact hh.symm

end CategoryTheory
