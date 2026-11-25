/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.OrdinaryCocycle
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # The ambient derived associator on representatives

The derived scalar associator, defined as a mate, is computed on every cochain
representative by the ordinary tensor balancing and the derived counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace WeilConjectures.FdIntegralScalarForward

variable {T : Scheme.{u}} {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)

/-- The derived counit on cochain representatives, as a natural transformation. -/
def pbcCounitNT : DerivedCategory.Q ⋙ pbcDerivedExtend φ ⟶
    (pbcExtend φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv (pbcDerivedExtend φ) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ _) (pbcExtensionCounit φ) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((pbcExtend φ).mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((pbcExtend φ).mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _).hom

theorem pbcCounitNT_app (P : CochainComplex (pbcModules T R) ℤ) :
    (pbcCounitNT φ).app P = pbcComplexCounit φ P := by
  simp [pbcCounitNT, pbcComplexCounit]

variable {B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (ψ : S ⟶ B) (χ : R ⟶ B)
  (hc : φ ≫ ψ = χ)

/-- The chain-level tensor balancing of iterated ordinary PBC scalar extension. -/
def pbcExtendCompC : (pbcExtend φ).mapHomologicalComplex (.up ℤ) ⋙
    (pbcExtend ψ).mapHomologicalComplex (.up ℤ) ≅ (pbcExtend χ).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (pbcExtendComp φ ψ χ hc) (.up ℤ)

/-- The derived scalar associator. -/
def pbcDerivedComp : pbcDerivedExtend φ ⋙ pbcDerivedExtend ψ ≅ pbcDerivedExtend χ :=
  Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ) (pbcDerivedScalarAdjunction ψ)
    (pbcDerivedScalarAdjunction χ) (pbcDerivedRestrictComp φ ψ χ hc)

section Abstract

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆
variable {A : Type u₁} {B' : Type u₂} {C : Type u₃}
  {DA : Type u₄} {DB : Type u₅} {DC : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B'] [Category.{v₃} C]
  [Category.{v₄} DA] [Category.{v₅} DB] [Category.{v₆} DC]

theorem leftAdjointCompIso_homEquiv {F₀₁ : DA ⥤ DB} {G₁₀ : DB ⥤ DA} {F₁₂ : DB ⥤ DC}
    {G₂₁ : DC ⥤ DB} {F₀₂ : DA ⥤ DC} {G₂₀ : DC ⥤ DA} (adj₀₁ : F₀₁ ⊣ G₁₀)
    (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀) (e : G₂₁ ⋙ G₁₀ ≅ G₂₀) (P : DA) (K : DC)
    (f : F₀₂.obj P ⟶ K) :
    (adj₀₁.comp adj₁₂).homEquiv _ _
        ((Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).hom.app P ≫ f) =
      adj₀₂.homEquiv _ _ f ≫ e.inv.app K := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hu : (adj₀₁.comp adj₁₂).unit.app P ≫ (G₂₁ ⋙ G₁₀).map
      ((Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).hom.app P) =
      adj₀₂.unit.app P ≫ e.inv.app _ :=
    (unit_conjugateEquiv_symm adj₀₂ (adj₀₁.comp adj₁₂) e.inv P).symm
  rw [hu, Category.assoc, Category.assoc]
  congr 1
  exact (e.inv.naturality f).symm

/-- The derived associator, as a mate, is normalized by the chain-level balancing. -/
theorem leftAdjointCompIso_normalized
    {F : A ⥤ B'} {R : B' ⥤ A} {G : B' ⥤ C} {S : C ⥤ B'} {H : A ⥤ C} {U : C ⥤ A}
    {FD : DA ⥤ DB} {RD : DB ⥤ DA} {GD : DB ⥤ DC} {SD : DC ⥤ DB} {HD : DA ⥤ DC}
    {UD : DC ⥤ DA} {QA : A ⥤ DA} {QB : B' ⥤ DB} {QC : C ⥤ DC}
    (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ U) (ad : FD ⊣ RD) (bd : GD ⊣ SD) (cd : HD ⊣ UD)
    (εF : QA ⋙ FD ⟶ F ⋙ QB) (εG : QB ⋙ GD ⟶ G ⋙ QC)
    (εH : ∀ P, HD.obj (QA.obj P) ⟶ QC.obj (H.obj P))
    (ρF : R ⋙ QA ⟶ QB ⋙ RD) (ρG : S ⋙ QB ⟶ QC ⋙ SD)
    (ρH : ∀ K, QA.obj (U.obj K) ⟶ UD.obj (QC.obj K))
    (hF : ∀ P K (f : F.obj P ⟶ K),
      ad.homEquiv _ _ (εF.app P ≫ QB.map f) = QA.map (a.homEquiv _ _ f) ≫ ρF.app K)
    (hG : ∀ P K (f : G.obj P ⟶ K),
      bd.homEquiv _ _ (εG.app P ≫ QC.map f) = QB.map (b.homEquiv _ _ f) ≫ ρG.app K)
    (hH : ∀ P K (f : H.obj P ⟶ K),
      cd.homEquiv _ _ (εH P ≫ QC.map f) = QA.map (c.homEquiv _ _ f) ≫ ρH K)
    (η : S ⋙ R ≅ U) (δ : SD ⋙ RD ≅ UD) (ν : ∀ P, G.obj (F.obj P) ⟶ H.obj P)
    (hν : ∀ P, (a.comp b).homEquiv _ _ (ν P) ≫ η.hom.app (H.obj P) = c.unit.app P)
    (hρ : ∀ K, ρF.app (S.obj K) ≫ RD.map (ρG.app K) ≫ δ.hom.app (QC.obj K) =
      QA.map (η.hom.app K) ≫ ρH K)
    (P : A) :
    (Adjunction.leftAdjointCompIso ad bd cd δ).hom.app (QA.obj P) ≫ εH P =
      GD.map (εF.app P) ≫ εG.app (F.obj P) ≫ QC.map (ν P) := by
  apply ((ad.comp bd).homEquiv _ _).injective
  rw [leftAdjointCompIso_homEquiv]
  have h1 := normalizedAdjunction_composition a b ad bd εF εG ρF ρG hF hG P (H.obj P) (ν P)
  rw [h1]
  have hc := hH P (H.obj P) (𝟙 _)
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id] at hc
  rw [hc]
  have hν' : (a.comp b).homEquiv _ _ (ν P) = c.unit.app P ≫ η.inv.app (H.obj P) := by
    rw [← hν P, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hρ' : ρF.app (S.obj (H.obj P)) ≫ RD.map (ρG.app (H.obj P)) =
      QA.map (η.hom.app (H.obj P)) ≫ ρH (H.obj P) ≫ δ.inv.app (QC.obj (H.obj P)) := by
    rw [← Iso.app_inv, ← Category.assoc (QA.map _), Iso.eq_comp_inv, Iso.app_hom,
      Category.assoc, hρ]
  rw [hν', QA.map_comp, Category.assoc, hρ']
  simp only [Category.assoc]
  rw [← QA.map_comp_assoc (η.inv.app _), Iso.inv_hom_id_app]
  erw [QA.map_id, Category.id_comp]

end Abstract

private theorem pbcExtendComp_mate (X : pbcModules T R) :
    ((pbcScalarAdjunction φ).comp (pbcScalarAdjunction ψ)).homEquiv _ _
        ((pbcExtendComp φ ψ χ hc).hom.app X) ≫
      (pbcRestrictComp φ ψ χ hc).hom.app ((pbcExtend χ).obj X) =
      (pbcScalarAdjunction χ).unit.app X := by
  have h := leftAdjointCompIso_homEquiv (pbcScalarAdjunction φ) (pbcScalarAdjunction ψ)
    (pbcScalarAdjunction χ) (pbcRestrictComp φ ψ χ hc) X _ (𝟙 _)
  rw [Category.comp_id, Adjunction.homEquiv_id] at h
  change ((pbcScalarAdjunction φ).comp (pbcScalarAdjunction ψ)).homEquiv _ _
    ((pbcExtendComp φ ψ χ hc).hom.app X) = _ at h
  rw [h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

set_option linter.flexible false in
private theorem pbcExtendCompC_mate (P : CochainComplex (pbcModules T R) ℤ) :
    (((pbcScalarAdjunction φ).mapHomologicalComplex (.up ℤ)).comp
        ((pbcScalarAdjunction ψ).mapHomologicalComplex (.up ℤ))).homEquiv _ _
        ((pbcExtendCompC φ ψ χ hc).hom.app P) ≫
      (Functor.mapHomologicalComplexCompIso (pbcRestrictComp φ ψ χ hc) (.up ℤ)).hom.app
        (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P) =
      ((pbcScalarAdjunction χ).mapHomologicalComplex (.up ℤ)).unit.app P := by
  apply HomologicalComplex.hom_ext
  intro n
  have h := pbcExtendComp_mate φ ψ χ hc (P.X n)
  rw [Adjunction.homEquiv_unit] at h ⊢
  simp [pbcExtendCompC]
  exact h

private theorem pbcRestrictComp_factors (K : CochainComplex (pbcModules T B) ℤ) :
    (pbcRestrict φ).mapDerivedCategoryFactors.inv.app
        (((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (pbcDerivedRestrict φ).map ((pbcRestrict ψ).mapDerivedCategoryFactors.inv.app K) ≫
      (pbcDerivedRestrictComp φ ψ χ hc).hom.app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (pbcRestrictComp φ ψ χ hc) (.up ℤ)).hom.app K) ≫
      (pbcRestrict χ).mapDerivedCategoryFactors.inv.app K := by
  rw [← cancel_mono ((pbcRestrict χ).mapDerivedCategoryFactors.hom.app K)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  dsimp only [pbcDerivedRestrictComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac]
  have hc' := Functor.mapDerivedCategoryCompIso_hom_app_factors (pbcRestrict ψ) (pbcRestrict φ) K
  have hc2 : ((pbcRestrict ψ).mapDerivedCategoryCompIso (pbcRestrict φ)).hom.app
      (DerivedCategory.Q.obj K) ≫
        (pbcRestrict ψ ⋙ pbcRestrict φ).mapDerivedCategoryFactors.hom.app K =
      (pbcRestrict φ).mapDerivedCategory.map ((pbcRestrict ψ).mapDerivedCategoryFactors.hom.app K) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcRestrict ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
    rw [← hc', Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hc2]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app_assoc, Category.comp_id]
  rfl

private theorem pbcTranspose (P : CochainComplex (pbcModules T R) ℤ)
    (K : CochainComplex (pbcModules T S) ℤ)
    (f : ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P ⟶ K) :
    (pbcDerivedScalarAdjunction φ).homEquiv _ _ ((pbcCounitNT φ).app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
          (((pbcScalarAdjunction φ).mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.inv.app K := by
  rw [pbcCounitNT_app]
  exact pbcAdjunction_complexTranspose T φ P K f

/-- The derived scalar associator on a cochain representative. -/
theorem pbcDerivedComp_counit (P : CochainComplex (pbcModules T R) ℤ) :
    (pbcDerivedComp φ ψ χ hc).hom.app (DerivedCategory.Q.obj P) ≫ (pbcCounitNT χ).app P =
      (pbcDerivedExtend ψ).map ((pbcCounitNT φ).app P) ≫
        (pbcCounitNT ψ).app (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((pbcExtendCompC φ ψ χ hc).hom.app P) :=
  leftAdjointCompIso_normalized
    ((pbcScalarAdjunction φ).mapHomologicalComplex (.up ℤ))
    ((pbcScalarAdjunction ψ).mapHomologicalComplex (.up ℤ))
    ((pbcScalarAdjunction χ).mapHomologicalComplex (.up ℤ))
    (pbcDerivedScalarAdjunction φ) (pbcDerivedScalarAdjunction ψ) (pbcDerivedScalarAdjunction χ)
    (pbcCounitNT φ) (pbcCounitNT ψ) (fun P ↦ (pbcCounitNT χ).app P)
    (pbcRestrict φ).mapDerivedCategoryFactors.inv (pbcRestrict ψ).mapDerivedCategoryFactors.inv
    (fun K ↦ (pbcRestrict χ).mapDerivedCategoryFactors.inv.app K)
    (pbcTranspose φ) (pbcTranspose ψ) (pbcTranspose χ)
    (Functor.mapHomologicalComplexCompIso (pbcRestrictComp φ ψ χ hc) (.up ℤ))
    (pbcDerivedRestrictComp φ ψ χ hc) (fun P ↦ (pbcExtendCompC φ ψ χ hc).hom.app P)
    (pbcExtendCompC_mate φ ψ χ hc) (pbcRestrictComp_factors φ ψ χ hc) P

end WeilConjectures.FdIntegralScalarForward
