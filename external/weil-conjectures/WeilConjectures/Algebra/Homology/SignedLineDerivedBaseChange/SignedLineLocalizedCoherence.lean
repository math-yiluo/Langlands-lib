/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
import all WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineOrdinaryConstraints
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import Mathlib.Tactic.CategoryTheory.Slice

/-! # Coherence of localized normalized line comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
-- Reuse tagged equalities when specializing the localization constraints.
set_option backward.defeqAttrib.useBackward true
set_option genSizeOf false
set_option genInjectivity false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules.SignedLineDerivedBaseChange
attribute [local irreducible] siteDerivedTensorIndependentCoefficients
  KFlatFixedTensor.representativeIso monoidalCategory
set_option allowUnsafeReducibility true in
attribute [local irreducible] KFlatFixedTensor.derivedTensor
  KFlatFixedTensor.selectedTensorPresentation
  KFlatFixedTensor.selectedResolvingTensorPresentation

attribute [local irreducible] derivedLine
  siteSheafTensorRight
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors Functor.leftAdjoint
    Functor.rightAdjoint

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}

section Abstract
universe ua va ub vb
variable {A₀ : Type ua} {B₀ : Type ub} [Category.{va} A₀] [Category.{vb} B₀]
  (L : A₀ ⥤ B₀) (W : MorphismProperty A₀) [L.IsLocalization W]
include W

private theorem lift_unit (F : A₀ ⥤ A₀) (D : B₀ ⥤ B₀)
    (c : L ⋙ D ≅ F ⋙ L) (u : F ≅ 𝟭 _) :
    ∃ d : D ≅ 𝟭 _, ∀ X, d.hom.app (L.obj X) = c.hom.app X ≫ L.map (u.hom.app X) := by
  let ψ : L ⋙ D ≅ L ⋙ 𝟭 _ := c ≪≫ Functor.isoWhiskerRight u L
  let d : D ≅ 𝟭 _ := Localization.liftNatIso L W _ _ D (𝟭 _) ψ
  refine ⟨d, ?_⟩
  intro X
  dsimp only [d, Localization.liftNatIso]
  simp only [Localization.liftNatTrans_app, Localization.Lifting.iso]
  simp [ψ]

private theorem lift_product (F G H : A₀ ⥤ A₀) (D E I : B₀ ⥤ B₀)
    (cF : L ⋙ D ≅ F ⋙ L) (cG : L ⋙ E ≅ G ⋙ L) (cH : L ⋙ I ≅ H ⋙ L)
    (p : F ⋙ G ≅ H) :
    ∃ d : D ⋙ E ≅ I, ∀ X, d.hom.app (L.obj X) ≫ cH.hom.app X =
      E.map (cF.hom.app X) ≫ cG.hom.app (F.obj X) ≫ L.map (p.hom.app X) := by
  let ψ : L ⋙ D ⋙ E ≅ L ⋙ I :=
    Functor.isoWhiskerRight cF E ≪≫ Functor.isoWhiskerLeft F cG ≪≫
      Functor.isoWhiskerRight p L ≪≫ cH.symm
  let d : D ⋙ E ≅ I := Localization.liftNatIso L W _ _ (D ⋙ E) I ψ
  have hd (X : A₀) : d.hom.app (L.obj X) = ψ.hom.app X := by
    dsimp only [d, Localization.liftNatIso]
    simp only [Localization.liftNatTrans_app, Localization.Lifting.iso]
    simp
  refine ⟨d, ?_⟩
  intro X
  rw [hd]
  simp only [ψ, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem lift_evaluation (F G : A₀ ⥤ A₀) (D E : B₀ ⥤ B₀)
    (cF : L ⋙ D ≅ F ⋙ L) (cG : L ⋙ E ≅ G ⋙ L) (e : F ⋙ G ⟶ 𝟭 _) :
    ∃ d : D ⋙ E ⟶ 𝟭 _, ∀ X, d.app (L.obj X) =
      E.map (cF.hom.app X) ≫ cG.hom.app (F.obj X) ≫ L.map (e.app X) := by
  let ψ : L ⋙ D ⋙ E ⟶ L ⋙ 𝟭 _ :=
    Functor.whiskerRight cF.hom E ≫ Functor.whiskerLeft F cG.hom ≫
      Functor.whiskerRight e L
  let d : D ⋙ E ⟶ 𝟭 _ := Localization.liftNatTrans L W _ _ (D ⋙ E) (𝟭 _) ψ
  refine ⟨d, ?_⟩
  intro X
  dsimp only [d]
  simp only [Localization.liftNatTrans_app, Localization.Lifting.iso]
  simp [ψ]

end Abstract

section LocalizedUnit
universe a₁ h₁ a₂ h₂ a₃ h₃ a₄ h₄
variable {A₁ : Type a₁} {A₂ : Type a₂} {A₃ : Type a₃} {A₄ : Type a₄}
  [Category.{h₁} A₁] [Category.{h₂} A₂] [Category.{h₃} A₃] [Category.{h₄} A₄]
private theorem localized_unit
    (L : A₁ ⥤ A₂) (W : MorphismProperty A₁) [L.IsLocalization W]
    (Q : A₃ ⥤ A₄) (F : A₁ ⥤ A₃) (DF : A₂ ⥤ A₄)
    (f : L ⋙ DF ≅ F ⋙ Q)
    (r : A₁ ⥤ A₁) (d : A₂ ⥤ A₂) (s : A₃ ⥤ A₃) (e : A₄ ⥤ A₄)
    (c : L ⋙ d ≅ r ⋙ L) (k : Q ⋙ e ≅ s ⋙ Q)
    (γ : r ⋙ F ≅ F ⋙ s) (η : d ⋙ DF ≅ DF ⋙ e)
    (ur : r ≅ 𝟭 _) (us : s ≅ 𝟭 _) (ud : d ≅ 𝟭 _) (ue : e ≅ 𝟭 _)
    (hd : ∀ X, ud.hom.app (L.obj X) = c.hom.app X ≫ L.map (ur.hom.app X))
    (he : ∀ X, ue.hom.app (Q.obj X) = k.hom.app X ≫ Q.map (us.hom.app X))
    (hη : ∀ X, η.hom.app (L.obj X) ≫ e.map (f.hom.app X) ≫ k.hom.app (F.obj X) =
      DF.map (c.hom.app X) ≫ f.hom.app (r.obj X) ≫ Q.map (γ.hom.app X))
    (ho : ∀ X, F.map (ur.hom.app X) = γ.hom.app X ≫ us.hom.app (F.obj X)) :
    ∀ X, η.hom.app X ≫ ue.hom.app (DF.obj X) = DF.map (ud.hom.app X) := by
  have h : η.hom ≫ Functor.whiskerLeft DF ue.hom = Functor.whiskerRight ud.hom DF := by
    apply Localization.natTrans_ext L W
    intro X
    change η.hom.app (L.obj X) ≫ ue.hom.app (DF.obj (L.obj X)) = _
    apply (cancel_mono (f.hom.app X)).mp
    have hn := ue.hom.naturality (f.hom.app X)
    change e.map (f.hom.app X) ≫ ue.hom.app (Q.obj (F.obj X)) =
      ue.hom.app (DF.obj (L.obj X)) ≫ f.hom.app X at hn
    rw [Category.assoc, ← hn, he]
    rw [← Category.assoc, ← Category.assoc, Category.assoc (η.hom.app _) _ _, hη]
    simp only [Category.assoc]
    rw [← Q.map_comp, ← ho]
    have hf := f.hom.naturality (ur.hom.app X)
    change DF.map (L.map (ur.hom.app X)) ≫ f.hom.app X =
      f.hom.app (r.obj X) ≫ Q.map (F.map (ur.hom.app X)) at hf
    rw [← hf]
    rw [← DF.map_comp_assoc, ← hd]
    rfl
  intro X
  exact congrArg (fun q ↦ q.app X) h
private theorem localized_product
    (L : A₁ ⥤ A₂) (W : MorphismProperty A₁) [L.IsLocalization W]
    (Q : A₃ ⥤ A₄) (F : A₁ ⥤ A₃) (DF : A₂ ⥤ A₄)
    (f : L ⋙ DF ≅ F ⋙ Q)
    (r₁ r₂ r₃ : A₁ ⥤ A₁) (d₁ d₂ d₃ : A₂ ⥤ A₂)
    (s₁ s₂ s₃ : A₃ ⥤ A₃) (e₁ e₂ e₃ : A₄ ⥤ A₄)
    (c₁ : L ⋙ d₁ ≅ r₁ ⋙ L) (c₂ : L ⋙ d₂ ≅ r₂ ⋙ L)
    (c₃ : L ⋙ d₃ ≅ r₃ ⋙ L)
    (k₁ : Q ⋙ e₁ ≅ s₁ ⋙ Q) (k₂ : Q ⋙ e₂ ≅ s₂ ⋙ Q)
    (k₃ : Q ⋙ e₃ ≅ s₃ ⋙ Q)
    (γ₁ : r₁ ⋙ F ≅ F ⋙ s₁) (γ₂ : r₂ ⋙ F ≅ F ⋙ s₂)
    (γ₃ : r₃ ⋙ F ≅ F ⋙ s₃)
    (η₁ : d₁ ⋙ DF ≅ DF ⋙ e₁) (η₂ : d₂ ⋙ DF ≅ DF ⋙ e₂)
    (η₃ : d₃ ⋙ DF ≅ DF ⋙ e₃)
    (pr : r₁ ⋙ r₂ ⟶ r₃) (ps : s₁ ⋙ s₂ ⟶ s₃)
    (pd : d₁ ⋙ d₂ ⟶ d₃) (pe : e₁ ⋙ e₂ ⟶ e₃)
    (hd : ∀ X, pd.app (L.obj X) ≫ c₃.hom.app X =
      d₂.map (c₁.hom.app X) ≫ c₂.hom.app (r₁.obj X) ≫ L.map (pr.app X))
    (he : ∀ X, pe.app (Q.obj X) ≫ k₃.hom.app X =
      e₂.map (k₁.hom.app X) ≫ k₂.hom.app (s₁.obj X) ≫ Q.map (ps.app X))
    (h₁ : ∀ X, η₁.hom.app (L.obj X) ≫ e₁.map (f.hom.app X) ≫ k₁.hom.app (F.obj X) =
      DF.map (c₁.hom.app X) ≫ f.hom.app (r₁.obj X) ≫ Q.map (γ₁.hom.app X))
    (h₂ : ∀ X, η₂.hom.app (L.obj X) ≫ e₂.map (f.hom.app X) ≫ k₂.hom.app (F.obj X) =
      DF.map (c₂.hom.app X) ≫ f.hom.app (r₂.obj X) ≫ Q.map (γ₂.hom.app X))
    (h₃ : ∀ X, η₃.hom.app (L.obj X) ≫ e₃.map (f.hom.app X) ≫ k₃.hom.app (F.obj X) =
      DF.map (c₃.hom.app X) ≫ f.hom.app (r₃.obj X) ≫ Q.map (γ₃.hom.app X))
    (ho : ∀ X, F.map (pr.app X) ≫ γ₃.hom.app X =
      γ₂.hom.app (r₁.obj X) ≫ s₂.map (γ₁.hom.app X) ≫ ps.app (F.obj X)) :
    ∀ X, DF.map (pd.app X) ≫ η₃.hom.app X =
      η₂.hom.app (d₁.obj X) ≫ e₂.map (η₁.hom.app X) ≫ pe.app (DF.obj X) := by
  have h : Functor.whiskerRight pd DF ≫ η₃.hom =
      Functor.whiskerLeft d₁ η₂.hom ≫ Functor.whiskerRight η₁.hom e₂ ≫
        Functor.whiskerLeft DF pe := by
    apply Localization.natTrans_ext L W
    intro X
    change DF.map (pd.app (L.obj X)) ≫ η₃.hom.app (L.obj X) = _
    apply (cancel_mono (e₃.map (f.hom.app X) ≫ k₃.hom.app (F.obj X))).mp
    have hn := pe.naturality (f.hom.app X)
    change e₂.map (e₁.map (f.hom.app X)) ≫ pe.app (Q.obj (F.obj X)) =
      pe.app (DF.obj (L.obj X)) ≫ e₃.map (f.hom.app X) at hn
    have hk := k₂.hom.naturality (γ₁.hom.app X)
    change e₂.map (Q.map (γ₁.hom.app X)) ≫ k₂.hom.app (s₁.obj (F.obj X)) =
      k₂.hom.app (F.obj (r₁.obj X)) ≫ Q.map (s₂.map (γ₁.hom.app X)) at hk
    have hη := η₂.hom.naturality (c₁.hom.app X)
    change DF.map (d₂.map (c₁.hom.app X)) ≫ η₂.hom.app (L.obj (r₁.obj X)) =
      η₂.hom.app (d₁.obj (L.obj X)) ≫ e₂.map (DF.map (c₁.hom.app X)) at hη
    have hf := f.hom.naturality (pr.app X)
    change DF.map (L.map (pr.app X)) ≫ f.hom.app (r₃.obj X) =
      f.hom.app (r₂.obj (r₁.obj X)) ≫ Q.map (F.map (pr.app X)) at hf
    simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Category.assoc]
    rw [h₃, ← DF.map_comp_assoc, hd]
    simp only [Functor.map_comp, Category.assoc]
    slice_rhs 3 4 => rw [← hn]
    rw [Category.assoc, he]
    slice_rhs 2 3 => rw [← e₂.map_comp]
    slice_rhs 2 3 => rw [← e₂.map_comp]
    rw [Category.assoc (η₁.hom.app _) _ _, h₁]
    simp only [Functor.map_comp, Category.assoc]
    slice_rhs 4 5 => rw [hk]
    slice_rhs 1 2 => rw [← hη]
    simp only [Category.assoc]
    slice_rhs 2 4 => rw [h₂]
    simp only [Category.assoc]
    slice_lhs 3 4 => rw [hf]
    slice_lhs 4 5 => rw [← Q.map_comp]
    slice_rhs 4 6 => rw [← Q.map_comp, ← Q.map_comp]
    rw [ho]
  intro X
  exact congrArg (fun q ↦ q.app X) h

private theorem localized_evaluation
    (L : A₁ ⥤ A₂) (W : MorphismProperty A₁) [L.IsLocalization W]
    (Q : A₃ ⥤ A₄) (F : A₁ ⥤ A₃) (DF : A₂ ⥤ A₄)
    (f : L ⋙ DF ≅ F ⋙ Q)
    (r₁ r₂ : A₁ ⥤ A₁) (d₁ d₂ : A₂ ⥤ A₂)
    (s₁ s₂ : A₃ ⥤ A₃) (e₁ e₂ : A₄ ⥤ A₄)
    (c₁ : L ⋙ d₁ ≅ r₁ ⋙ L) (c₂ : L ⋙ d₂ ≅ r₂ ⋙ L)
    (k₁ : Q ⋙ e₁ ≅ s₁ ⋙ Q) (k₂ : Q ⋙ e₂ ≅ s₂ ⋙ Q)
    (γ₁ : r₁ ⋙ F ≅ F ⋙ s₁) (γ₂ : r₂ ⋙ F ≅ F ⋙ s₂)
    (η₁ : d₁ ⋙ DF ≅ DF ⋙ e₁) (η₂ : d₂ ⋙ DF ≅ DF ⋙ e₂)
    (pr : r₁ ⋙ r₂ ⟶ 𝟭 _) (ps : s₁ ⋙ s₂ ⟶ 𝟭 _)
    (pd : d₁ ⋙ d₂ ⟶ 𝟭 _) (pe : e₁ ⋙ e₂ ⟶ 𝟭 _)
    (hd : ∀ X, pd.app (L.obj X) =
      d₂.map (c₁.hom.app X) ≫ c₂.hom.app (r₁.obj X) ≫ L.map (pr.app X))
    (he : ∀ X, pe.app (Q.obj X) =
      e₂.map (k₁.hom.app X) ≫ k₂.hom.app (s₁.obj X) ≫ Q.map (ps.app X))
    (h₁ : ∀ X, η₁.hom.app (L.obj X) ≫ e₁.map (f.hom.app X) ≫ k₁.hom.app (F.obj X) =
      DF.map (c₁.hom.app X) ≫ f.hom.app (r₁.obj X) ≫ Q.map (γ₁.hom.app X))
    (h₂ : ∀ X, η₂.hom.app (L.obj X) ≫ e₂.map (f.hom.app X) ≫ k₂.hom.app (F.obj X) =
      DF.map (c₂.hom.app X) ≫ f.hom.app (r₂.obj X) ≫ Q.map (γ₂.hom.app X))
    (ho : ∀ X, F.map (pr.app X) =
      γ₂.hom.app (r₁.obj X) ≫ s₂.map (γ₁.hom.app X) ≫ ps.app (F.obj X)) :
    ∀ X, DF.map (pd.app X) =
      η₂.hom.app (d₁.obj X) ≫ e₂.map (η₁.hom.app X) ≫ pe.app (DF.obj X) := by
  have h : Functor.whiskerRight pd DF =
      Functor.whiskerLeft d₁ η₂.hom ≫ Functor.whiskerRight η₁.hom e₂ ≫
        Functor.whiskerLeft DF pe := by
    apply Localization.natTrans_ext L W
    intro X
    change DF.map (pd.app (L.obj X)) = _
    apply (cancel_mono (f.hom.app X)).mp
    have hn := pe.naturality (f.hom.app X)
    change e₂.map (e₁.map (f.hom.app X)) ≫ pe.app (Q.obj (F.obj X)) =
      pe.app (DF.obj (L.obj X)) ≫ f.hom.app X at hn
    have hk := k₂.hom.naturality (γ₁.hom.app X)
    change e₂.map (Q.map (γ₁.hom.app X)) ≫ k₂.hom.app (s₁.obj (F.obj X)) =
      k₂.hom.app (F.obj (r₁.obj X)) ≫ Q.map (s₂.map (γ₁.hom.app X)) at hk
    have hη := η₂.hom.naturality (c₁.hom.app X)
    change DF.map (d₂.map (c₁.hom.app X)) ≫ η₂.hom.app (L.obj (r₁.obj X)) =
      η₂.hom.app (d₁.obj (L.obj X)) ≫ e₂.map (DF.map (c₁.hom.app X)) at hη
    have hf := f.hom.naturality (pr.app X)
    change DF.map (L.map (pr.app X)) ≫ f.hom.app X =
      f.hom.app (r₂.obj (r₁.obj X)) ≫ Q.map (F.map (pr.app X)) at hf
    simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Category.assoc]
    rw [hd]
    simp only [Functor.map_comp, Category.assoc]
    slice_rhs 3 4 => rw [← hn]
    rw [he]
    slice_rhs 2 3 => rw [← e₂.map_comp]
    slice_rhs 2 3 => rw [← e₂.map_comp]
    rw [Category.assoc (η₁.hom.app _) _ _, h₁]
    simp only [Functor.map_comp, Category.assoc]
    slice_rhs 4 5 => rw [hk]
    slice_rhs 1 2 => rw [← hη]
    simp only [Category.assoc]
    slice_rhs 2 4 => rw [h₂]
    simp only [Category.assoc]
    slice_lhs 3 4 => rw [hf]
    slice_rhs 4 6 => rw [← Q.map_comp, ← Q.map_comp]
    rw [ho]
  intro X
  exact congrArg (fun q ↦ q.app X) h

private theorem localized_family
    (L : A₁ ⥤ A₂) (W : MorphismProperty A₁) [L.IsLocalization W]
    (Q : A₃ ⥤ A₄) (F : A₁ ⥤ A₃) (DF : A₂ ⥤ A₄)
    (f : L ⋙ DF ≅ F ⋙ Q)
    (r : ℤ → A₁ ⥤ A₁) (d : ℤ → A₂ ⥤ A₂)
    (s : ℤ → A₃ ⥤ A₃) (e : ℤ → A₄ ⥤ A₄)
    (c : ∀ i, L ⋙ d i ≅ r i ⋙ L) (k : ∀ i, Q ⋙ e i ≅ s i ⋙ Q)
    (g : ∀ i, r i ⋙ F ≅ F ⋙ s i) (eta : ∀ i, d i ⋙ DF ≅ DF ⋙ e i)
    (ur : r 0 ≅ 𝟭 _) (us : s 0 ≅ 𝟭 _) (ud : d 0 ≅ 𝟭 _) (ue : e 0 ≅ 𝟭 _)
    (pr : ∀ n : ℕ, r (.ofNat (n + 1)) ⋙ r 1 ⟶ r (.ofNat (n + 2)))
    (ps : ∀ n : ℕ, s (.ofNat (n + 1)) ⋙ s 1 ⟶ s (.ofNat (n + 2)))
    (pd : ∀ n : ℕ, d (.ofNat (n + 1)) ⋙ d 1 ⟶ d (.ofNat (n + 2)))
    (pe : ∀ n : ℕ, e (.ofNat (n + 1)) ⋙ e 1 ⟶ e (.ofNat (n + 2)))
    (er : ∀ n : ℕ, r (.negSucc n) ⋙ r (.ofNat (n + 1)) ⟶ 𝟭 _)
    (es : ∀ n : ℕ, s (.negSucc n) ⋙ s (.ofNat (n + 1)) ⟶ 𝟭 _)
    (ed : ∀ n : ℕ, d (.negSucc n) ⋙ d (.ofNat (n + 1)) ⟶ 𝟭 _)
    (ee : ∀ n : ℕ, e (.negSucc n) ⋙ e (.ofNat (n + 1)) ⟶ 𝟭 _)
    (hdu : ∀ X, ud.hom.app (L.obj X) = (c 0).hom.app X ≫ L.map (ur.hom.app X))
    (heu : ∀ X, ue.hom.app (Q.obj X) = (k 0).hom.app X ≫ Q.map (us.hom.app X))
    (hdp : ∀ n X, (pd n).app (L.obj X) ≫ (c (.ofNat (n + 2))).hom.app X =
      (d 1).map ((c (.ofNat (n + 1))).hom.app X) ≫
        (c 1).hom.app ((r (.ofNat (n + 1))).obj X) ≫ L.map ((pr n).app X))
    (hep : ∀ n X, (pe n).app (Q.obj X) ≫ (k (.ofNat (n + 2))).hom.app X =
      (e 1).map ((k (.ofNat (n + 1))).hom.app X) ≫
        (k 1).hom.app ((s (.ofNat (n + 1))).obj X) ≫ Q.map ((ps n).app X))
    (hde : ∀ n X, (ed n).app (L.obj X) =
      (d (.ofNat (n + 1))).map ((c (.negSucc n)).hom.app X) ≫
        (c (.ofNat (n + 1))).hom.app ((r (.negSucc n)).obj X) ≫ L.map ((er n).app X))
    (hee : ∀ n X, (ee n).app (Q.obj X) =
      (e (.ofNat (n + 1))).map ((k (.negSucc n)).hom.app X) ≫
        (k (.ofNat (n + 1))).hom.app ((s (.negSucc n)).obj X) ≫ Q.map ((es n).app X))
    (hsq : ∀ i X, (eta i).hom.app (L.obj X) ≫ (e i).map (f.hom.app X) ≫ (k i).hom.app (F.obj X) =
      DF.map ((c i).hom.app X) ≫ f.hom.app ((r i).obj X) ≫ Q.map ((g i).hom.app X))
    (hou : ∀ X, F.map (ur.hom.app X) = (g 0).hom.app X ≫ us.hom.app (F.obj X))
    (hop : ∀ n X, F.map ((pr n).app X) ≫ (g (.ofNat (n + 2))).hom.app X =
      (g 1).hom.app ((r (.ofNat (n + 1))).obj X) ≫
        (s 1).map ((g (.ofNat (n + 1))).hom.app X) ≫ (ps n).app (F.obj X))
    (hoe : ∀ n X, F.map ((er n).app X) =
      (g (.ofNat (n + 1))).hom.app ((r (.negSucc n)).obj X) ≫
        (s (.ofNat (n + 1))).map ((g (.negSucc n)).hom.app X) ≫ (es n).app (F.obj X)) :
    (∀ X, (eta 0).hom.app X ≫ ue.hom.app (DF.obj X) = DF.map (ud.hom.app X)) ∧
    (∀ n X, DF.map ((pd n).app X) ≫ (eta (.ofNat (n + 2))).hom.app X =
      (eta 1).hom.app ((d (.ofNat (n + 1))).obj X) ≫
        (e 1).map ((eta (.ofNat (n + 1))).hom.app X) ≫ (pe n).app (DF.obj X)) ∧
    (∀ n X, DF.map ((ed n).app X) =
      (eta (.ofNat (n + 1))).hom.app ((d (.negSucc n)).obj X) ≫
        (e (.ofNat (n + 1))).map ((eta (.negSucc n)).hom.app X) ≫ (ee n).app (DF.obj X)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact localized_unit L W Q F DF f _ _ _ _ (c 0) (k 0) (g 0) (eta 0)
      ur us ud ue hdu heu (hsq 0) hou
  · intro n
    exact localized_product L W Q F DF f _ _ _ _ _ _ _ _ _ _ _ _
      (c (.ofNat (n + 1))) (c 1) (c (.ofNat (n + 2)))
      (k (.ofNat (n + 1))) (k 1) (k (.ofNat (n + 2)))
      (g (.ofNat (n + 1))) (g 1) (g (.ofNat (n + 2)))
      (eta (.ofNat (n + 1))) (eta 1) (eta (.ofNat (n + 2)))
      (pr n) (ps n) (pd n) (pe n) (hdp n) (hep n)
      (hsq _) (hsq _) (hsq _) (hop n)
  · intro n
    exact localized_evaluation L W Q F DF f _ _ _ _ _ _ _ _
      (c (.negSucc n)) (c (.ofNat (n + 1)))
      (k (.negSucc n)) (k (.ofNat (n + 1)))
      (g (.negSucc n)) (g (.ofNat (n + 1)))
      (eta (.negSucc n)) (eta (.ofNat (n + 1)))
      (er n) (es n) (ed n) (ee n) (hde n) (hee n) (hsq _) (hsq _) (hoe n)

end LocalizedUnit

section ComplexConstraints
universe ac hc
variable {AA : Type ac} [Category.{hc} AA] [HasZeroMorphisms AA]
private def complex_unit (F : AA ⥤ AA) [F.PreservesZeroMorphisms]
    (e : F ≅ 𝟭 _) : F.mapHomologicalComplex (.up ℤ) ≅ 𝟭 _ :=
  NatIso.mapHomologicalComplex e (.up ℤ)
private def complex_product (F G H : AA ⥤ AA)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (e : F ⋙ G ≅ H) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex e (.up ℤ)
private def complex_evaluation (F G : AA ⥤ AA)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (e : F ⋙ G ⟶ 𝟭 _) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ⟶ 𝟭 _ :=
  NatTrans.mapHomologicalComplex e (.up ℤ)
end ComplexConstraints
section ComplexCoherence
universe ac hc bc kc
variable {AA : Type ac} [Category.{hc} AA] [HasZeroMorphisms AA]

universe da dah db dbh
private theorem complex_family_constraints
    {DA : Type da} {DB : Type db} [Category.{dah} DA] [Category.{dbh} DB]
    {BB : Type bc} [Category.{kc} BB] [HasZeroMorphisms BB]
    (L : CochainComplex AA ℤ ⥤ DA)
    (W : MorphismProperty (CochainComplex AA ℤ)) [L.IsLocalization W]
    (Q : CochainComplex BB ℤ ⥤ DB)
    (V : MorphismProperty (CochainComplex BB ℤ)) [Q.IsLocalization V]
    (F : AA ⥤ BB) [F.PreservesZeroMorphisms] (DF : DA ⥤ DB)
    (f : L ⋙ DF ≅ F.mapHomologicalComplex (.up ℤ) ⋙ Q)
    (r : ℤ → AA ⥤ AA) (d : ℤ → DA ⥤ DA)
    (s : ℤ → BB ⥤ BB) (e : ℤ → DB ⥤ DB)
    [∀ i, (r i).PreservesZeroMorphisms] [∀ i, (s i).PreservesZeroMorphisms]
    (c : ∀ i, L ⋙ d i ≅ (r i).mapHomologicalComplex (.up ℤ) ⋙ L)
    (k : ∀ i, Q ⋙ e i ≅ (s i).mapHomologicalComplex (.up ℤ) ⋙ Q)
    (g : ∀ i, r i ⋙ F ≅ F ⋙ s i) (eta : ∀ i, d i ⋙ DF ≅ DF ⋙ e i)
    (ur : r 0 ≅ 𝟭 _) (us : s 0 ≅ 𝟭 _)
    (pr : ∀ n : ℕ, r (.ofNat (n + 1)) ⋙ r 1 ≅ r (.ofNat (n + 2)))
    (ps : ∀ n : ℕ, s (.ofNat (n + 1)) ⋙ s 1 ≅ s (.ofNat (n + 2)))
    (er : ∀ n : ℕ, r (.negSucc n) ⋙ r (.ofNat (n + 1)) ⟶ 𝟭 _)
    (es : ∀ n : ℕ, s (.negSucc n) ⋙ s (.ofNat (n + 1)) ⟶ 𝟭 _)
    (hsq : ∀ i X,
      (eta i).hom.app (L.obj X) ≫ (e i).map (f.hom.app X) ≫
          (k i).hom.app ((F.mapHomologicalComplex (.up ℤ)).obj X) =
        DF.map ((c i).hom.app X) ≫
          f.hom.app (((r i).mapHomologicalComplex (.up ℤ)).obj X) ≫
          Q.map ((NatIso.mapHomologicalComplex (g i) (.up ℤ)).hom.app X))
    (hou : ∀ X, F.map (ur.hom.app X) = (g 0).hom.app X ≫ us.hom.app (F.obj X))
    (hop : ∀ n X, F.map ((pr n).hom.app X) ≫ (g (.ofNat (n + 2))).hom.app X =
      (g 1).hom.app ((r (.ofNat (n + 1))).obj X) ≫
        (s 1).map ((g (.ofNat (n + 1))).hom.app X) ≫ (ps n).hom.app (F.obj X))
    (hoe : ∀ n X, F.map ((er n).app X) =
      (g (.ofNat (n + 1))).hom.app ((r (.negSucc n)).obj X) ≫
        (s (.ofNat (n + 1))).map ((g (.negSucc n)).hom.app X) ≫
        (es n).app (F.obj X))
    (ordinaryR : (r 0 ≅ 𝟭 _) →
      (∀ n : ℕ, r (.ofNat (n + 1)) ⋙ r 1 ≅ r (.ofNat (n + 2))) →
      (∀ n : ℕ, r (.negSucc n) ⋙ r (.ofNat (n + 1)) ⟶ 𝟭 _) → Prop)
    (ordinaryS : (s 0 ≅ 𝟭 _) →
      (∀ n : ℕ, s (.ofNat (n + 1)) ⋙ s 1 ≅ s (.ofNat (n + 2))) →
      (∀ n : ℕ, s (.negSucc n) ⋙ s (.ofNat (n + 1)) ⟶ 𝟭 _) → Prop)
    (hoR : ordinaryR ur pr er) (hoS : ordinaryS us ps es) :
    LocalizedLineFamily d e DF eta
      (LocalizedLineConstraints L r d ordinaryR c)
      (LocalizedLineConstraints Q s e ordinaryS k) := by
  obtain ⟨ud, h0⟩ := lift_unit L W _ _ (c 0) (complex_unit _ ur)
  obtain ⟨ue, h1⟩ := lift_unit Q V _ _ (k 0) (complex_unit _ us)
  choose pd h2 using fun n : ℕ ↦ lift_product L W _ _ _ _ _ _
    (c (.ofNat (n + 1))) (c 1) (c (.ofNat (n + 2)))
    (complex_product _ _ _ (pr n))
  choose pe h3 using fun n : ℕ ↦ lift_product Q V _ _ _ _ _ _
    (k (.ofNat (n + 1))) (k 1) (k (.ofNat (n + 2)))
    (complex_product _ _ _ (ps n))
  choose ed h4 using fun n : ℕ ↦ lift_evaluation L W _ _ _ _
    (c (.negSucc n)) (c (.ofNat (n + 1))) (complex_evaluation _ _ (er n))
  choose ee h5 using fun n : ℕ ↦ lift_evaluation Q V _ _ _ _
    (k (.negSucc n)) (k (.ofNat (n + 1))) (complex_evaluation _ _ (es n))
  have h := localized_family L W Q (F.mapHomologicalComplex (.up ℤ)) DF f
    (fun i ↦ (r i).mapHomologicalComplex (.up ℤ)) d
    (fun i ↦ (s i).mapHomologicalComplex (.up ℤ)) e c k
    (fun i ↦ NatIso.mapHomologicalComplex (g i) (.up ℤ)) eta
    (complex_unit _ ur) (complex_unit _ us) ud ue
    (fun n ↦ (complex_product _ _ _ (pr n)).hom)
    (fun n ↦ (complex_product _ _ _ (ps n)).hom)
    (fun n ↦ (pd n).hom) (fun n ↦ (pe n).hom)
    (fun n ↦ complex_evaluation _ _ (er n))
    (fun n ↦ complex_evaluation _ _ (es n)) ed ee h0 h1 h2 h3 h4 h5 hsq
    (by intro X; apply HomologicalComplex.Hom.ext; funext i; exact hou (X.X i))
    (by intro n X; apply HomologicalComplex.Hom.ext; funext i; exact hop n (X.X i))
    (by intro n X; apply HomologicalComplex.Hom.ext; funext i; exact hoe n (X.X i))
  refine LocalizedLineFamily.mk ud ue pd pe ed ee ?_ ?_ h.1 h.2.1 h.2.2
  · exact LocalizedLineConstraints.mk ur pr er hoR
      (fun E ↦ heq_of_eq (h0 E)) (fun n E ↦ heq_of_eq (h2 n E))
      (fun n E ↦ heq_of_eq (h4 n E))
  · exact LocalizedLineConstraints.mk us ps es hoS
      (fun E ↦ heq_of_eq (h1 E)) (fun n E ↦ heq_of_eq (h3 n E))
      (fun n E ↦ heq_of_eq (h5 n E))

end ComplexCoherence
attribute [local irreducible] DerivedCategory.Q
  MorphismProperty.HasLocalization.L MorphismProperty.Q'
  DerivedCategory HomologicalComplex.quasiIso

variable
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
  (t : (pull a).obj P ≅ Q)

private theorem section_map {M N : KFlatFixedTensor.Modules R} (f : M ⟶ N)
    (V : C) (x : M.val.obj (op V)) :
    ((pull a).map f).val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a) M V x) =
    ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a) N V
      (f.val.app (op V) x) := by
  let := module_pushforward_isRightAdjoint_of_universes a
  exact (congrArg (fun g ↦ g.val.app (op V) x)
    ((pullbackPushforwardAdjunction a).unit.naturality f)).symm

private theorem section_smul (M : KFlatFixedTensor.Modules R) (V : C)
    (r : R.obj.obj (op V)) (x : M.val.obj (op V)) :
    ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
      M V (r • x) =
    a.hom.app (op V) r • ringedSitePullbackSection a
      (module_pushforward_isRightAdjoint_of_universes a) M V x := by
  let := module_pushforward_isRightAdjoint_of_universes a
  exact (((pullbackPushforwardAdjunction a).unit.app M).val.app (op V)).hom.map_smul r x

private theorem action_square
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S)
    (γ : siteSheafTensorRight L ⋙ F ≅ F ⋙ siteSheafTensorRight M)
    (b : DerivedActionData.{u, v, w, z} F L M)
    (h : DerivedAction.{u, v, w, z} F L M γ b)
    : DerivedActionSquare.{u, v, w, z} F L M γ b := by
  unfold DerivedAction at h
  obtain ⟨hL, hM, hLf, hMf, hR, hS, hsq, huq⟩ := h
  exact hsq

private theorem ordinary_family_coherence
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
      signedLinePower.{u, v, w} Q d)
    (hT : SignedLinePullbackNormalized a P Q t T)
    (γ : ∀ d : ℤ, siteSheafTensorRight (signedLinePower.{u, v, w} P d) ⋙ pull a ≅
      pull a ⋙ siteSheafTensorRight (signedLinePower.{u, v, w} Q d))
    (hγ : (∀ (d : ℤ) (M : KFlatFixedTensor.Modules R) (V : C) (x : M.val.obj (op V))
            (y : (signedLinePower.{u, v, w} P d).val.obj (op V)),
            ((γ d).hom.app M).val.app (op (U.obj V))
                (ringedSitePullbackSection a
                  (module_pushforward_isRightAdjoint_of_universes a)
                  ((siteSheafTensorRight (signedLinePower.{u, v, w} P d)).obj M) V
                  (siteSheafTensorTmul M (signedLinePower.{u, v, w} P d) (op V) x y)) =
              siteSheafTensorTmul ((pull a).obj M) (signedLinePower.{u, v, w} Q d)
                (op (U.obj V))
                (ringedSitePullbackSection a
                  (module_pushforward_isRightAdjoint_of_universes a) M V x)
                ((T d).hom.val.app (op (U.obj V))
                  (ringedSitePullbackSection a
                    (module_pushforward_isRightAdjoint_of_universes a)
                    (signedLinePower.{u, v, w} P d) V y))))
    (ouR : siteSheafTensorRight (signedLinePower.{u, v, w} P 0) ≅ 𝟭 _)
    (ouS : siteSheafTensorRight (signedLinePower.{u, v, w} Q 0) ≅ 𝟭 _)
    (opR : ∀ n : ℕ,
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} P 1) ≅
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 2))))
    (opS : ∀ n : ℕ,
      siteSheafTensorRight (signedLinePower.{u, v, w} Q (.ofNat (n + 1))) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} Q 1) ≅
      siteSheafTensorRight (signedLinePower.{u, v, w} Q (.ofNat (n + 2))))
    (oeR : ∀ n : ℕ,
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.negSucc n)) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⟶ 𝟭 _)
    (oeS : ∀ n : ℕ,
      siteSheafTensorRight (signedLinePower.{u, v, w} Q (.negSucc n)) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} Q (.ofNat (n + 1))) ⟶ 𝟭 _)
    (hoR : OrdinaryLineConstraints.{u, v, w} R P ouR opR oeR)
    (hoS : OrdinaryLineConstraints.{u, v, w} S Q ouS opS oeS) :
    (∀ (M : KFlatFixedTensor.Modules R),
      (pull a).map (ouR.hom.app M) =
        (γ 0).hom.app M ≫ ouS.hom.app ((pull a).obj M)) ∧
    (∀ (n : ℕ) (M : KFlatFixedTensor.Modules R),
      (pull a).map ((opR n).hom.app M) ≫ (γ (.ofNat (n + 2))).hom.app M =
        (γ 1).hom.app ((siteSheafTensorRight
            (signedLinePower.{u, v, w} P (.ofNat (n + 1)))).obj M) ≫
          (siteSheafTensorRight (signedLinePower.{u, v, w} Q 1)).map
            ((γ (.ofNat (n + 1))).hom.app M) ≫
          (opS n).hom.app ((pull a).obj M)) ∧
    (∀ (n : ℕ) (M : KFlatFixedTensor.Modules R),
      (pull a).map ((oeR n).app M) =
        (γ (.ofNat (n + 1))).hom.app
            ((siteSheafTensorRight (signedLinePower.{u, v, w} P (.negSucc n))).obj M) ≫
          (siteSheafTensorRight (signedLinePower.{u, v, w} Q (.ofNat (n + 1)))).map
            ((γ (.negSucc n)).hom.app M) ≫
          (oeS n).app ((pull a).obj M)) := by
  let := module_pushforward_isRightAdjoint_of_universes a
  obtain ⟨huR, hpR, heR⟩ := hoR
  obtain ⟨huS, hpS, heS⟩ := hoS
  have hou (M : KFlatFixedTensor.Modules R) :
      (pull a).map (ouR.hom.app M) =
        (γ 0).hom.app M ≫ ouS.hom.app ((pull a).obj M) := by
    apply (pullbackPushforwardAdjunction a).homEquiv _ _ |>.injective
    apply scalarTensor_hom_ext
    intro V x r
    change ((pull a).map (ouR.hom.app M)).val.app (op (U.obj V.unop))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        ((siteSheafTensorRight (signedLinePower.{u, v, w} P 0)).obj M) V.unop
          (siteSheafTensorTmul M _ V x r)) =
      (ouS.hom.app ((pull a).obj M)).val.app (op (U.obj V.unop))
        (((γ 0).hom.app M).val.app (op (U.obj V.unop))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            ((siteSheafTensorRight (signedLinePower.{u, v, w} P 0)).obj M) V.unop
              (siteSheafTensorTmul M _ V x r)))
    conv_lhs => erw [section_map, huR, section_smul]
    conv_rhs => erw [hγ, huS, hT.1]
    rfl
  -- The positive square is determined on three pure factors.
  have hop (n : ℕ) (M : KFlatFixedTensor.Modules R) :
      (pull a).map ((opR n).hom.app M) ≫ (γ (.ofNat (n + 2))).hom.app M =
        (γ 1).hom.app ((siteSheafTensorRight
            (signedLinePower.{u, v, w} P (.ofNat (n + 1)))).obj M) ≫
          (siteSheafTensorRight (signedLinePower.{u, v, w} Q 1)).map
            ((γ (.ofNat (n + 1))).hom.app M) ≫
          (opS n).hom.app ((pull a).obj M) := by
    apply (pullbackPushforwardAdjunction a).homEquiv _ _ |>.injective
    apply tensor_three_ext.{u, v, w} R
    intro V x y q
    change ((γ (.ofNat (n + 2))).hom.app M).val.app (op (U.obj V.unop))
      (((pull a).map ((opR n).hom.app M)).val.app (op (U.obj V.unop))
        (ringedSitePullbackSection a _ _ V.unop
          (siteSheafTensorTmul _ P V (siteSheafTensorTmul M _ V x y) q))) =
      ((opS n).hom.app ((pull a).obj M)).val.app (op (U.obj V.unop))
        (((siteSheafTensorRight (signedLinePower.{u, v, w} Q 1)).map
            ((γ (.ofNat (n + 1))).hom.app M)).val.app (op (U.obj V.unop))
          (((γ 1).hom.app _).val.app (op (U.obj V.unop))
            (ringedSitePullbackSection a _ _ V.unop
              (siteSheafTensorTmul _ P V (siteSheafTensorTmul M _ V x y) q))))
    conv_lhs => erw [section_map, hpR, hγ]
    conv_rhs => erw [hγ, scalarTensor_first_tmul, hγ, hpS]
    erw [hT.2.2.1]
    erw [hT.2.1]
    rfl
  have hoe (n : ℕ) (M : KFlatFixedTensor.Modules R) :
      (pull a).map ((oeR n).app M) =
        (γ (.ofNat (n + 1))).hom.app
            ((siteSheafTensorRight (signedLinePower.{u, v, w} P (.negSucc n))).obj M) ≫
          (siteSheafTensorRight (signedLinePower.{u, v, w} Q (.ofNat (n + 1)))).map
            ((γ (.negSucc n)).hom.app M) ≫
          (oeS n).app ((pull a).obj M) := by
    apply (pullbackPushforwardAdjunction a).homEquiv _ _ |>.injective
    apply tensor_three_ext.{u, v, w} R
    intro V x phi y
    change ((pull a).map ((oeR n).app M)).val.app (op (U.obj V.unop))
      (ringedSitePullbackSection a _ _ V.unop
        (siteSheafTensorTmul _ _ V (siteSheafTensorTmul M _ V x phi) y)) =
      ((oeS n).app ((pull a).obj M)).val.app (op (U.obj V.unop))
        (((siteSheafTensorRight _).map ((γ (.negSucc n)).hom.app M)).val.app
          (op (U.obj V.unop))
          (((γ (.ofNat (n + 1))).hom.app _).val.app (op (U.obj V.unop))
            (ringedSitePullbackSection a _ _ V.unop
              (siteSheafTensorTmul _ _ V (siteSheafTensorTmul M _ V x phi) y))))
    rw [section_map]
    change ringedSitePullbackSection a _ M V.unop
      (((oeR n).app M).val.app V
        (siteSheafTensorTmul _ (scalarTensorPower R P (n + 1)) V
          (siteSheafTensorTmul M (signedLinePower.{u, v, w} P (.negSucc n)) V x phi) y)) = _
    rw [heR]
    erw [section_smul]
    conv_rhs => erw [hγ, scalarTensor_first_tmul, hγ, heS, hT.2.2.2]
    rfl
  exact ⟨hou, hop, hoe⟩

attribute [local irreducible] signedLinePower scalarTensorPower homObj unit

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem derived_family_of_ordinary
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
    (γ : ∀ d : ℤ, siteSheafTensorRight (signedLinePower.{u, v, w} P d) ⋙ F ≅
      F ⋙ siteSheafTensorRight (signedLinePower.{u, v, w} Q d))
    (b : ∀ d : ℤ, DerivedActionData.{u, v, w, z} F (signedLinePower.{u, v, w} P d)
      (signedLinePower.{u, v, w} Q d))
    (hb : ∀ d : ℤ, DerivedAction.{u, v, w, z} F (signedLinePower.{u, v, w} P d)
      (signedLinePower.{u, v, w} Q d) (γ d) (b d))
    (ouR : siteSheafTensorRight (signedLinePower.{u, v, w} P 0) ≅ 𝟭 _)
    (ouS : siteSheafTensorRight (signedLinePower.{u, v, w} Q 0) ≅ 𝟭 _)
    (opR : ∀ n : ℕ,
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} P 1) ≅
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 2))))
    (opS : ∀ n : ℕ,
      siteSheafTensorRight (signedLinePower.{u, v, w} Q (.ofNat (n + 1))) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} Q 1) ≅
      siteSheafTensorRight (signedLinePower.{u, v, w} Q (.ofNat (n + 2))))
    (oeR : ∀ n : ℕ,
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.negSucc n)) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⟶ 𝟭 _)
    (oeS : ∀ n : ℕ,
      siteSheafTensorRight (signedLinePower.{u, v, w} Q (.negSucc n)) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} Q (.ofNat (n + 1))) ⟶ 𝟭 _)
    (hoR : OrdinaryLineConstraints.{u, v, w} R P ouR opR oeR)
    (hoS : OrdinaryLineConstraints.{u, v, w} S Q ouS opS oeS)
    (hou : ∀ (M : KFlatFixedTensor.Modules R),
      F.map (ouR.hom.app M) =
        (γ 0).hom.app M ≫ ouS.hom.app (F.obj M))
    (hop : ∀ (n : ℕ) (M : KFlatFixedTensor.Modules R),
      F.map ((opR n).hom.app M) ≫ (γ (.ofNat (n + 2))).hom.app M =
        (γ 1).hom.app ((siteSheafTensorRight
            (signedLinePower.{u, v, w} P (.ofNat (n + 1)))).obj M) ≫
          (siteSheafTensorRight (signedLinePower.{u, v, w} Q 1)).map
            ((γ (.ofNat (n + 1))).hom.app M) ≫
          (opS n).hom.app (F.obj M))
    (hoe : ∀ (n : ℕ) (M : KFlatFixedTensor.Modules R),
      F.map ((oeR n).app M) =
        (γ (.ofNat (n + 1))).hom.app
            ((siteSheafTensorRight (signedLinePower.{u, v, w} P (.negSucc n))).obj M) ≫
          (siteSheafTensorRight (signedLinePower.{u, v, w} Q (.ofNat (n + 1)))).map
            ((γ (.negSucc n)).hom.app M) ≫
          (oeS n).app (F.obj M))
    : DerivedFamilyCoherence.{u, v, w, z} F P Q b := by
  let L : CochainComplex (KFlatFixedTensor.Modules R) ℤ ⥤
      DerivedCategory.{z} (KFlatFixedTensor.Modules R) := DerivedCategory.Q
  let Z : CochainComplex (KFlatFixedTensor.Modules S) ℤ ⥤
      DerivedCategory.{z} (KFlatFixedTensor.Modules S) := DerivedCategory.Q
  let W := HomologicalComplex.quasiIso (KFlatFixedTensor.Modules R) (.up ℤ)
  let Fc : CochainComplex (KFlatFixedTensor.Modules R) ℤ ⥤
      CochainComplex (KFlatFixedTensor.Modules S) ℤ :=
    F.mapHomologicalComplex (.up ℤ)
  let DF : DerivedCategory.{z} (KFlatFixedTensor.Modules R) ⥤
      DerivedCategory.{z} (KFlatFixedTensor.Modules S) := F.mapDerivedCategory
  let f : L ⋙ DF ≅ Fc ⋙ Z := F.mapDerivedCategoryFactors
  let dR (d : ℤ) : DerivedCategory.{z} (KFlatFixedTensor.Modules R) ⥤
      DerivedCategory.{z} (KFlatFixedTensor.Modules R) :=
    derivedLine.{u, v, w, z} R (signedLinePower.{u, v, w} P d)
  let dS (d : ℤ) : DerivedCategory.{z} (KFlatFixedTensor.Modules S) ⥤
      DerivedCategory.{z} (KFlatFixedTensor.Modules S) :=
    derivedLine.{u, v, w, z} S (signedLinePower.{u, v, w} Q d)
  have hsquare (d : ℤ) (E : CochainComplex (KFlatFixedTensor.Modules R) ℤ) :=
    eq_of_heq (action_square F (signedLinePower.{u, v, w} P d)
      (signedLinePower.{u, v, w} Q d) (γ d) (b d) (hb d) E)
  exact @complex_family_constraints
    (KFlatFixedTensor.Modules R) inferInstance inferInstance
    (DerivedCategory.{z} (KFlatFixedTensor.Modules R))
    (DerivedCategory.{z} (KFlatFixedTensor.Modules S)) inferInstance inferInstance
    (KFlatFixedTensor.Modules S) inferInstance inferInstance
    L W inferInstance Z (HomologicalComplex.quasiIso (KFlatFixedTensor.Modules S) (.up ℤ))
    inferInstance F inferInstance DF f
    (fun d ↦ siteSheafTensorRight (signedLinePower.{u, v, w} P d)) dR
    (fun d ↦ siteSheafTensorRight (signedLinePower.{u, v, w} Q d)) dS
    (fun d ↦ siteSheafTensorRight_preservesZeroMorphisms _)
    (fun d ↦ siteSheafTensorRight_preservesZeroMorphisms _)
    (fun d ↦ (b d).1) (fun d ↦ (b d).2.1) γ (fun d ↦ (b d).2.2)
    ouR ouS opR opS oeR oeS (by intro d E; exact hsquare d E) hou hop hoe
    (OrdinaryLineConstraints R P) (OrdinaryLineConstraints S Q) hoR hoS

/-- Normalized ordinary line comparisons yield coherent derived line actions.
Source: Stacks Project, Tags 03EL, 0FNY and 07A4; Powers and duals, step 11.
(blueprint: lem-pur-signed-line-localized-coherence)
Proof: construct the ordinary unit, positive-power reassociation and dual evaluation.
Their pure-tensor formulas determine them. The normalization of T and the pure-tensor
formula for gamma make the three ordinary squares commute, by tensor generation and
the module pullback adjunction. Lift these constraints through the quasi-isomorphism
localization using the two comparisons in b. On every localized complex, the square
in DerivedAction replaces each eta by the corresponding termwise gamma. The three
resulting diagrams are the images under Q of the ordinary squares. Localization
whiskering is faithful, so the diagrams hold on every derived object. The prescribed
representative normalizations of b make these precisely DerivedLineConstraints. -/
theorem signed_line_localized_coherence
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
      signedLinePower.{u, v, w} Q d)
    (hT : SignedLinePullbackNormalized a P Q t T)
    [hAdd : (pull a).Additive] [hLim : PreservesFiniteLimits (pull a)]
    [hCol : PreservesFiniteColimits (pull a)]
    (γ : ∀ d : ℤ, siteSheafTensorRight (signedLinePower.{u, v, w} P d) ⋙ pull a ≅
      pull a ⋙ siteSheafTensorRight (signedLinePower.{u, v, w} Q d))
    (hγ : (∀ (d : ℤ) (M : KFlatFixedTensor.Modules R) (V : C) (x : M.val.obj (op V))
            (y : (signedLinePower.{u, v, w} P d).val.obj (op V)),
            ((γ d).hom.app M).val.app (op (U.obj V))
                (ringedSitePullbackSection a
                  (module_pushforward_isRightAdjoint_of_universes a)
                  ((siteSheafTensorRight (signedLinePower.{u, v, w} P d)).obj M) V
                  (siteSheafTensorTmul M (signedLinePower.{u, v, w} P d) (op V) x y)) =
              siteSheafTensorTmul ((pull a).obj M) (signedLinePower.{u, v, w} Q d)
                (op (U.obj V))
                (ringedSitePullbackSection a
                  (module_pushforward_isRightAdjoint_of_universes a) M V x)
                ((T d).hom.val.app (op (U.obj V))
                  (ringedSitePullbackSection a
                    (module_pushforward_isRightAdjoint_of_universes a)
                    (signedLinePower.{u, v, w} P d) V y))))
    (b : ∀ d : ℤ, DerivedActionData.{u, v, w, z} (pull a) (signedLinePower.{u, v, w} P d)
      (signedLinePower.{u, v, w} Q d))
    (hb : ∀ d : ℤ, DerivedAction.{u, v, w, z} (pull a) (signedLinePower.{u, v, w} P d)
      (signedLinePower.{u, v, w} Q d) (γ d) (b d)) :
    DerivedFamilyCoherence.{u, v, w, z} (pull a) P Q b := by
  let := module_pushforward_isRightAdjoint_of_universes a
  obtain ⟨ouR, opR, oeR, huR, hpR, heR⟩ :=
    signed_line_ordinary_constraints.{u, v, w} R P
  obtain ⟨ouS, opS, oeS, huS, hpS, heS⟩ :=
    signed_line_ordinary_constraints.{u, v, w} S Q
  have hoR : OrdinaryLineConstraints.{u, v, w} R P ouR opR oeR := ⟨huR, hpR, heR⟩
  have hoS : OrdinaryLineConstraints.{u, v, w} S Q ouS opS oeS := ⟨huS, hpS, heS⟩
  obtain ⟨hou, hop, hoe⟩ := ordinary_family_coherence a P Q t T hT γ hγ
    ouR ouS opR opS oeR oeS hoR hoS
  exact derived_family_of_ordinary (pull a) P Q γ b hb
    ouR ouS opR opS oeR oeS hoR hoS hou hop hoe

end SheafOfModules.SignedLineDerivedBaseChange
