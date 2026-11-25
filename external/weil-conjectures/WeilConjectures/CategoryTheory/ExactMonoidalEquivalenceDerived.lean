/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Equivalence
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-! Coherent monoidal descent of an exact monoidal equivalence. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory
namespace ExactMonoidalEquivalenceDerived

section DescentConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Category Functor.LaxMonoidal Functor.OplaxMonoidal
section
variable {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory H]
  (Q₁ : C ⥤ D) (Q₂ : E ⥤ H) (F : C ⥤ E) (G : D ⥤ H)
  [Q₁.LaxMonoidal] [Q₂.LaxMonoidal] [F.Monoidal] [G.Monoidal]
  [IsIso (ε Q₂)] (e : Q₁ ⋙ G ⟶ F ⋙ Q₂)
  (hη : η G = G.map (ε Q₁) ≫ e.app (𝟙_ C) ≫ Q₂.map (η F) ≫ inv (ε Q₂))
  (hδ : ∀ X Y, δ G (Q₁.obj X) (Q₁.obj Y) ≫
    (e.app X ⊗ₘ e.app Y) ≫ μ Q₂ (F.obj X) (F.obj Y) =
    G.map (μ Q₁ X Y) ≫ e.app (X ⊗ Y) ≫ Q₂.map (δ F X Y))

include hη hδ in
private theorem square_monoidal : NatTrans.IsMonoidal e where
  unit := by
    simp only [Functor.LaxMonoidal.comp_ε, assoc]
    change ε G ≫ G.map (ε Q₁) ≫ e.app (𝟙_ C) = ε Q₂ ≫ Q₂.map (ε F)
    rw [← cancel_mono (Q₂.map (η F))]
    simp only [assoc, ← Q₂.map_comp, Functor.Monoidal.ε_η,
      CategoryTheory.Functor.map_id, comp_id]
    rw [← cancel_mono (inv (ε Q₂))]
    simp only [assoc, ← hη, Functor.Monoidal.ε_η, IsIso.hom_inv_id]
  tensor X Y := by
    simp only [Functor.LaxMonoidal.comp_μ, assoc]
    change μ G (Q₁.obj X) (Q₁.obj Y) ≫ G.map (μ Q₁ X Y) ≫ e.app (X ⊗ Y) =
      (e.app X ⊗ₘ e.app Y) ≫ μ Q₂ (F.obj X) (F.obj Y) ≫ Q₂.map (μ F X Y)
    rw [← cancel_epi (δ G (Q₁.obj X) (Q₁.obj Y))]
    simp only [Functor.Monoidal.δ_μ_assoc]
    rw [← cancel_mono (Q₂.map (δ F X Y))]
    simp only [assoc, ← Q₂.map_comp, Functor.Monoidal.μ_δ,
      CategoryTheory.Functor.map_id, comp_id]
    exact (hδ X Y).symm

end

section
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (e : F ⟶ G)
  (hη : e.app (𝟙_ C) ≫ η G = η F)
  (hδ : ∀ X Y, e.app (X ⊗ Y) ≫ δ G X Y = δ F X Y ≫ (e.app X ⊗ₘ e.app Y))
include hη hδ in
private theorem monoidal_of_oplax : NatTrans.IsMonoidal e where
  unit := by
    rw [← cancel_mono (η G), assoc, hη, Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]
  tensor X Y := by
    rw [← cancel_mono (δ G X Y), assoc, hδ, Functor.Monoidal.μ_δ_assoc, assoc,
      Functor.Monoidal.μ_δ, comp_id]
end

section
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category D₀] [Category D₁] [Category D₂]
  {Q₁ : C₀ ⥤ C₁} {Q₂ : C₁ ⥤ C₂} {R₁ : D₀ ⥤ D₁} {R₂ : D₁ ⥤ D₂}
  {L : C₀ ⥤ C₂} {M : D₀ ⥤ D₂}
  {F₀ : C₀ ⥤ D₀} {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂}
  (a : Q₁ ⋙ Q₂ ≅ L) (b : R₁ ⋙ R₂ ≅ M)
  (e₀ : Q₁ ⋙ F₁ ≅ F₀ ⋙ R₁) (e₁ : Q₂ ⋙ F₂ ≅ F₁ ⋙ R₂)

private def composeFactors : L ⋙ F₂ ≅ F₀ ⋙ M :=
  Functor.isoWhiskerRight a.symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft Q₁ e₁ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e₀ _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F₀ b

private theorem composeFactors_hom_app (K : C₀) :
    (composeFactors a b e₀ e₁).hom.app K =
      F₂.map (a.inv.app K) ≫ e₁.hom.app (Q₁.obj K) ≫
        R₂.map (e₀.hom.app K) ≫ b.hom.app (F₀.obj K) := by
  simp only [composeFactors, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp]

variable [MonoidalCategory C₀] [MonoidalCategory C₁] [MonoidalCategory C₂]
  [MonoidalCategory D₀] [MonoidalCategory D₁] [MonoidalCategory D₂]
  [Q₁.LaxMonoidal] [Q₂.LaxMonoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
  [L.LaxMonoidal] [M.LaxMonoidal] [F₀.LaxMonoidal] [F₁.LaxMonoidal] [F₂.LaxMonoidal]
  [NatTrans.IsMonoidal a.hom] [NatTrans.IsMonoidal b.hom]
  [NatTrans.IsMonoidal e₀.hom] [NatTrans.IsMonoidal e₁.hom]

private theorem composeFactors_monoidal :
    NatTrans.IsMonoidal (composeFactors a b e₀ e₁).hom := by
  dsimp only [composeFactors, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

end

section DerivedMonoidal

universe v uC uD

variable {A : Type uC} [Category.{v + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{v + 1} A] [MonoidalCategory A] [MonoidalClosed A]
    [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
    {B : Type uD} [Category.{v + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{v + 1} B] [MonoidalCategory B] [MonoidalClosed B]
    [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
    (F : A ⥤ B) [F.Additive] [F.Monoidal] [F.IsEquivalence]

private local instance : F.PreservesFlat := F.preservesFlat_of_isEquivalence

@[instance_reducible]
private noncomputable def mapHomotopyEquivalenceMonoidal :
    (F.mapHomotopyCategory (.up ℤ)).Monoidal := by
  letI : (F.mapHomotopyCategory (.up ℤ)).OplaxMonoidal :=
    Functor.mapHomotopyCategoryOplaxMonoidal F
  have : IsIso (Functor.OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) := by
    rw [Functor.mapHomotopyCategory_η]
    infer_instance
  have (X Y : HomotopyCategory A (.up ℤ)) :
      IsIso (Functor.OplaxMonoidal.δ (F.mapHomotopyCategory (.up ℤ)) X Y) :=
    inferInstanceAs (IsIso (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans
      (.up ℤ) F).app X).app Y))
  exact .ofOplaxMonoidal _

attribute [local instance] mapHomotopyEquivalenceMonoidal

@[instance_reducible]
private noncomputable def leftDerivedEquivalenceMonoidal : F.leftDerivedFunctor.Monoidal := by
  have := DerivedCategory.isIso_ε_Qh A
  have := DerivedCategory.isIso_ε_Qh B
  letI o : F.leftDerivedFunctor.OplaxMonoidal :=
    Functor.OplaxMonoidal.ofLaxSquare (Q₁ := DerivedCategory.Qh)
      (Q₂ := DerivedCategory.Qh) (F := F.mapHomotopyCategory (.up ℤ))
      F.leftDerivedTensorComparison (fun P ↦ F.leftDerivedFunctorCounit.app P)
      (fun _ _ f ↦ F.leftDerivedFunctorCounit.naturality f)
      F.leftDerivedTensorComparison_app_app_comp_tensorHom F.kFlatMap
      (fun X ↦ by
        obtain ⟨P, _, hFP, he⟩ := DerivedCategory.exists_kFlat_iso_of_isEquivalence F X
        exact ⟨P, hFP, he⟩)
      (fun X _ hP ↦ Functor.isIso_μNatTrans_Qh_app_app_of_kFlat X _ hP)
  have (X Y : DerivedCategory A) : IsIso (Functor.OplaxMonoidal.δ F.leftDerivedFunctor X Y) :=
    inferInstanceAs (IsIso ((F.leftDerivedTensorComparison.app X).app Y))
  have : IsIso (Functor.OplaxMonoidal.η F.leftDerivedFunctor) := by
    exact inferInstanceAs (IsIso (F.leftDerivedFunctor.map
      (Functor.LaxMonoidal.ε DerivedCategory.Qh) ≫ F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
        DerivedCategory.Qh.map
          (Functor.OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) ≫
            inv (Functor.LaxMonoidal.ε DerivedCategory.Qh)))
  exact .ofOplaxMonoidal _

attribute [local instance] leftDerivedEquivalenceMonoidal

@[instance_reducible]
private noncomputable def derivedEquivalenceMonoidal : F.mapDerivedCategory.Monoidal :=
  Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory

attribute [local instance] derivedEquivalenceMonoidal

private theorem leftDerivedCounit_monoidal :
    NatTrans.IsMonoidal F.leftDerivedFunctorCounit := by
  have := DerivedCategory.isIso_ε_Qh B
  apply square_monoidal DerivedCategory.Qh DerivedCategory.Qh
    (F.mapHomotopyCategory (.up ℤ)) F.leftDerivedFunctor F.leftDerivedFunctorCounit
  · rfl
  · exact F.leftDerivedTensorComparison_app_app_comp_tensorHom

private theorem derivedFactorsh_monoidal :
    NatTrans.IsMonoidal F.mapDerivedCategoryFactorsh.hom := by
  have hc : NatTrans.IsMonoidal F.leftDerivedFunctorCounit := leftDerivedCounit_monoidal F
  have hm : NatTrans.IsMonoidal F.leftDerivedFunctorIsoMapDerivedCategory.hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport F.leftDerivedFunctorIsoMapDerivedCategory
  have hi : NatTrans.IsMonoidal F.leftDerivedFunctorIsoMapDerivedCategory.inv := inferInstance
  have h : F.mapDerivedCategoryFactorsh.hom =
      (Functor.isoWhiskerLeft DerivedCategory.Qh
        F.leftDerivedFunctorIsoMapDerivedCategory.symm).hom ≫
          F.leftDerivedFunctorCounit := by
    apply NatTrans.ext
    funext K
    have hf := NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    simp only [NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Iso.symm_hom, ← hf, Iso.inv_hom_id_app_assoc]
  rw [h]
  dsimp only [Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  apply NatTrans.IsMonoidal.comp

omit [Abelian.HasFunctorialFlatResolution A] [Abelian.HasFunctorialFlatResolution B] in
private theorem mapHomotopyFactors_monoidal :
    NatTrans.IsMonoidal (F.mapHomotopyCategoryFactors (.up ℤ)).hom := by
  apply monoidal_of_oplax
  · change 𝟙 _ ≫ (HomotopyCategory.quotient B (.up ℤ)).map
        (η (F.mapHomologicalComplex (.up ℤ))) ≫ 𝟙 _ =
      (F.mapHomotopyCategory (.up ℤ)).map (𝟙 _) ≫
        (HomotopyCategory.quotient B (.up ℤ)).map (η (F.mapHomologicalComplex (.up ℤ)))
    rw [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]
  · intro K L
    change 𝟙 _ ≫ (HomotopyCategory.quotient B (.up ℤ)).map
        (δ (F.mapHomologicalComplex (.up ℤ)) K L) ≫ 𝟙 _ =
      ((F.mapHomotopyCategory (.up ℤ)).map (𝟙 _) ≫
        (HomotopyCategory.quotient B (.up ℤ)).map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app K).app L)) ≫
        (𝟙 _ ⊗ₘ 𝟙 _)
    rw [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    erw [tensorHom_id, id_whiskerRight, Category.comp_id]
    rfl

private theorem quotientCompQh_monoidal :
    NatTrans.IsMonoidal (DerivedCategory.quotientCompQhIso A).hom where
  unit := rfl
  tensor K L := by
    change μ ((HomotopyCategory.quotient A (.up ℤ)) ⋙ DerivedCategory.Qh) K L ≫
        (DerivedCategory.quotientCompQhIso A).hom.app (K ⊗ L) =
      ((DerivedCategory.quotientCompQhIso A).hom.app K ⊗ₘ
        (DerivedCategory.quotientCompQhIso A).hom.app L) ≫
      (((DerivedCategory.quotientCompQhIso A).inv.app K ⊗ₘ
        (DerivedCategory.quotientCompQhIso A).inv.app L) ≫
      μ ((HomotopyCategory.quotient A (.up ℤ)) ⋙ DerivedCategory.Qh) K L ≫
        (DerivedCategory.quotientCompQhIso A).hom.app (K ⊗ L))
    simp only [← Category.assoc, tensorHom_comp_tensorHom,
      Iso.hom_inv_id_app, tensorHom_id, id_whiskerRight, Category.id_comp]

end DerivedMonoidal
section Factors
universe v uC uD
variable {A : Type uC} [Category.{v + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{v + 1} A] [MonoidalCategory A] [MonoidalClosed A]
    [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
    {B : Type uD} [Category.{v + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{v + 1} B] [MonoidalCategory B] [MonoidalClosed B]
    [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
    (F : A ⥤ B) [F.Additive] [F.Monoidal] [F.IsEquivalence]
    [(F.mapHomotopyCategory (.up ℤ)).Monoidal] [F.mapDerivedCategory.Monoidal]
    [NatTrans.IsMonoidal (F.mapHomotopyCategoryFactors (.up ℤ)).hom]
    [NatTrans.IsMonoidal F.mapDerivedCategoryFactorsh.hom]

private noncomputable local instance : (F.mapHomologicalComplex (.up ℤ)).Monoidal :=
  Functor.mapCochainComplexMonoidal F
private noncomputable local instance :
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).LaxMonoidal :=
  Functor.LaxMonoidal.comp _ _
private theorem derivedFactors_monoidal :
    NatTrans.IsMonoidal F.mapDerivedCategoryFactors.hom := by
  have hc : NatTrans.IsMonoidal (DerivedCategory.quotientCompQhIso A).hom :=
    quotientCompQh_monoidal
  have hd : NatTrans.IsMonoidal (DerivedCategory.quotientCompQhIso B).hom :=
    quotientCompQh_monoidal
  let e := composeFactors (DerivedCategory.quotientCompQhIso A)
    (DerivedCategory.quotientCompQhIso B) (F.mapHomotopyCategoryFactors (.up ℤ))
    F.mapDerivedCategoryFactorsh
  have he : e.hom = F.mapDerivedCategoryFactors.hom := by
    apply NatTrans.ext
    funext K
    rw [composeFactors_hom_app]
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [Iso.inv_hom_id_app]
    exact Category.comp_id _
  rw [← he]
  apply composeFactors_monoidal (DerivedCategory.quotientCompQhIso A)
    (DerivedCategory.quotientCompQhIso B) (F.mapHomotopyCategoryFactors (.up ℤ))
    F.mapDerivedCategoryFactorsh

end Factors

section LeftData
universe v uA uB
variable {A : Type uA} [Category.{v + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{v + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type uB} [Category.{v + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{v + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  (F : A ⥤ B) [F.Additive] [F.Monoidal] [F.IsEquivalence]

private structure LeftData where
  [homotopyMonoidal : (F.mapHomotopyCategory (.up ℤ)).Monoidal]
  [derivedMonoidal : F.mapDerivedCategory.Monoidal]
  homotopyFactors : NatTrans.IsMonoidal (F.mapHomotopyCategoryFactors (.up ℤ)).hom
  derivedFactors : NatTrans.IsMonoidal F.mapDerivedCategoryFactorsh.hom

private theorem left_data : Nonempty (LeftData F) := by
  let := mapHomotopyEquivalenceMonoidal F
  let := derivedEquivalenceMonoidal F
  exact ⟨{ homotopyFactors := mapHomotopyFactors_monoidal F
           derivedFactors := derivedFactorsh_monoidal F }⟩
end LeftData
end DescentConstruction

section MateConstruction
open CategoryTheory MonoidalCategory
variable {A₀ B₀ A₁ B₁ : Type*} [Category A₀] [Category B₀] [Category A₁] [Category B₁]
  {F₀ : A₀ ⥤ B₀} {G₀ : B₀ ⥤ A₀} {F₁ : A₁ ⥤ B₁} {G₁ : B₁ ⥤ A₁}
  (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁)
  (Q : A₀ ⥤ A₁) (R : B₀ ⥤ B₁) (eF : Q ⋙ F₁ ≅ F₀ ⋙ R)
  [IsIso adj₀.counit] [IsIso adj₁.unit]

private noncomputable def rightMateIso : G₀ ⋙ Q ≅ R ⋙ G₁ :=
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft (G₀ ⋙ Q) (asIso adj₁.unit) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator G₀ Q F₁ ≪≫ Functor.isoWhiskerLeft G₀ eF ≪≫
        (Functor.associator _ _ _).symm) G₁ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerRight (asIso adj₀.counit) (R ⋙ G₁) ≪≫
    Functor.leftUnitor _

private theorem rightMateIso_hom_app (Y : B₀) :
    (rightMateIso adj₀ adj₁ Q R eF).hom.app Y =
      adj₁.unit.app (Q.obj (G₀.obj Y)) ≫ G₁.map (eF.hom.app (G₀.obj Y)) ≫
        G₁.map (R.map (adj₀.counit.app Y)) := by
  simp only [rightMateIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.symm_hom, asIso_hom, Category.id_comp, Category.comp_id]
  erw [Category.comp_id]
  rfl

variable (eG : R ⋙ G₁ ≅ G₀ ⋙ Q)
  (hu : ∀ X : A₀, adj₁.unit.app (Q.obj X) ≫ G₁.map (eF.hom.app X) ≫
    eG.hom.app (F₀.obj X) = Q.map (adj₀.unit.app X))

include hu in
private theorem rightMateIso_hom_eq : (rightMateIso adj₀ adj₁ Q R eF).hom = eG.inv := by
  apply NatTrans.ext
  funext Y
  rw [rightMateIso_hom_app]
  apply (cancel_mono (eG.hom.app Y)).1
  rw [Iso.inv_hom_id_app]
  have hn := eG.hom.naturality (adj₀.counit.app Y)
  change G₁.map (R.map (adj₀.counit.app Y)) ≫ eG.hom.app Y =
    eG.hom.app (F₀.obj (G₀.obj Y)) ≫ Q.map (G₀.map (adj₀.counit.app Y)) at hn
  simp only [Category.assoc] at hu ⊢
  rw [hn, reassoc_of% hu (G₀.obj Y), ← Q.map_comp,
    adj₀.right_triangle_components, CategoryTheory.Functor.map_id]
  rfl

variable [MonoidalCategory A₀] [MonoidalCategory B₀]
  [MonoidalCategory A₁] [MonoidalCategory B₁]
  [F₀.Monoidal] [G₀.LaxMonoidal] [F₁.Monoidal] [G₁.LaxMonoidal]
  [Q.LaxMonoidal] [R.LaxMonoidal] [NatTrans.IsMonoidal adj₀.counit]
  [NatTrans.IsMonoidal adj₁.unit] [NatTrans.IsMonoidal eF.hom]

private theorem rightMateIso_monoidal :
    NatTrans.IsMonoidal (rightMateIso adj₀ adj₁ Q R eF).hom := by
  dsimp only [rightMateIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, asIso_hom]
  infer_instance

section RightMonoidal
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Monoidal] (adj : F ⊣ G)
  [IsIso adj.unit] [IsIso adj.counit]

@[instance_reducible]
private noncomputable def rightMonoidal : G.Monoidal := by
  let := adj.rightAdjointLaxMonoidal
  have : adj.IsMonoidal := inferInstance
  have : IsIso (Functor.LaxMonoidal.ε G) := adj.isIso_ε_of_isIso_η
  have (X Y : D) : IsIso (Functor.LaxMonoidal.μ G X Y) := adj.isIso_μ_of_isIso_δ X Y
  exact .ofLaxMonoidal G

private theorem rightMonoidal_adj :
    let := rightMonoidal adj
    adj.IsMonoidal := by
  change letI := adj.rightAdjointLaxMonoidal; adj.IsMonoidal
  infer_instance

private structure RightData where
  [monoidal : G.Monoidal]
  adjunctionMonoidal : adj.IsMonoidal

private theorem right_data : Nonempty (RightData adj) := by
  let := rightMonoidal adj
  exact ⟨{ adjunctionMonoidal := rightMonoidal_adj adj }⟩
end RightMonoidal

section Descent
universe v uA uB
open CategoryTheory.Limits
variable {A : Type uA} [Category.{v + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{v + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type uB} [Category.{v + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{v + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] [F.Monoidal] [G.Monoidal]
  [F.IsEquivalence] [G.IsEquivalence] (adj : F ⊣ G)
private local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A
private local instance : HasColimitsOfSize.{0, 0} B := hasColimitsOfSizeShrink B
private noncomputable local instance : (F.mapHomologicalComplex (.up ℤ)).Monoidal :=
  Functor.mapCochainComplexMonoidal F
private noncomputable local instance : (G.mapHomologicalComplex (.up ℤ)).Monoidal :=
  Functor.mapCochainComplexMonoidal G

private noncomputable local instance :
    (G.mapHomologicalComplex (.up ℤ) ⋙ F.mapHomologicalComplex (.up ℤ)).LaxMonoidal :=
  Functor.LaxMonoidal.comp _ _

variable [IsIso adj.unit] [IsIso adj.counit]
omit [IsGrothendieckAbelian.{v + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  [IsGrothendieckAbelian.{v + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  [F.Monoidal] [G.Monoidal] [F.IsEquivalence] [IsIso adj.unit] [IsIso adj.counit] in
private theorem complexCounit_iso : IsIso (adj.mapHomologicalComplex (.up ℤ)).counit := by
  have (K : CochainComplex B ℤ) :
      IsIso ((adj.mapHomologicalComplex (.up ℤ)).counit.app K) := by
    have (n : ℤ) : IsIso (((adj.mapHomologicalComplex (.up ℤ)).counit.app K).f n) :=
      inferInstanceAs (IsIso (adj.counit.app (K.X n)))
    exact HomologicalComplex.Hom.isIso_of_components _
  exact NatIso.isIso_of_isIso_app _

omit [IsGrothendieckAbelian.{v + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  [IsGrothendieckAbelian.{v + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  [F.Monoidal] [G.Monoidal] [G.IsEquivalence] [IsIso adj.unit] [IsIso adj.counit] in
private theorem hcUnit_iso : IsIso (adj.mapHomotopyCategory (.up ℤ)).unit := by
  have (K : CochainComplex A ℤ) :
      IsIso ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) := by
    have (n : ℤ) : IsIso (((adj.mapHomologicalComplex (.up ℤ)).unit.app K).f n) :=
      inferInstanceAs (IsIso (adj.unit.app (K.X n)))
    exact HomologicalComplex.Hom.isIso_of_components _
  have (P : HomotopyCategory A (.up ℤ)) :
      IsIso ((adj.mapHomotopyCategory (.up ℤ)).unit.app P) := by
    obtain ⟨K, rfl⟩ := P.quotient_obj_surjective
    rw [adj.mapHomotopyCategory_unit_app_quotient (.up ℤ) K]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

omit [IsGrothendieckAbelian.{v + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  [IsGrothendieckAbelian.{v + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  [F.Monoidal] [G.Monoidal] [F.IsEquivalence] [IsIso adj.unit] [IsIso adj.counit] in
private theorem hcCounit_iso : IsIso (adj.mapHomotopyCategory (.up ℤ)).counit := by
  have hi : IsIso (adj.mapHomologicalComplex (.up ℤ)).counit := complexCounit_iso adj
  have (P : HomotopyCategory B (.up ℤ)) :
      IsIso ((adj.mapHomotopyCategory (.up ℤ)).counit.app P) := by
    obtain ⟨K, rfl⟩ := P.quotient_obj_surjective
    rw [adj.mapHomotopyCategory_counit_app_quotient (.up ℤ) K]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

variable [(F.mapHomotopyCategory (.up ℤ)).Monoidal]
  [(G.mapHomotopyCategory (.up ℤ)).Monoidal]

omit [Abelian.HasFunctorialFlatResolution A] [Abelian.HasFunctorialFlatResolution B]
  [IsIso adj.unit] [IsIso adj.counit] in
private theorem inverseHC_factors
    [IsIso (adj.mapHomologicalComplex (.up ℤ)).counit]
    [IsIso (adj.mapHomotopyCategory (.up ℤ)).unit]
    [NatTrans.IsMonoidal (adj.mapHomologicalComplex (.up ℤ)).counit]
    [NatTrans.IsMonoidal (adj.mapHomotopyCategory (.up ℤ)).unit]
    [NatTrans.IsMonoidal (F.mapHomotopyCategoryFactors (.up ℤ)).hom] :
    NatTrans.IsMonoidal (G.mapHomotopyCategoryFactors (.up ℤ)).hom := by
  have hm := rightMateIso_monoidal (adj.mapHomologicalComplex (.up ℤ))
    (adj.mapHomotopyCategory (.up ℤ)) (HomotopyCategory.quotient A (.up ℤ))
    (HomotopyCategory.quotient B (.up ℤ)) (F.mapHomotopyCategoryFactors (.up ℤ))
  have he := rightMateIso_hom_eq (adj.mapHomologicalComplex (.up ℤ))
    (adj.mapHomotopyCategory (.up ℤ)) (HomotopyCategory.quotient A (.up ℤ))
    (HomotopyCategory.quotient B (.up ℤ)) (F.mapHomotopyCategoryFactors (.up ℤ))
    (G.mapHomotopyCategoryFactors (.up ℤ)) (by
      intro K
      change (adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≫
          (G.mapHomotopyCategory (.up ℤ)).map (𝟙 _) ≫ 𝟙 _ = _
      erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
      exact adj.mapHomotopyCategory_unit_app_quotient (.up ℤ) K)
  rw [he] at hm
  have : NatTrans.IsMonoidal (G.mapHomotopyCategoryFactors (.up ℤ)).symm.hom := hm
  exact inferInstanceAs
    (NatTrans.IsMonoidal (G.mapHomotopyCategoryFactors (.up ℤ)).symm.inv)

variable [F.mapDerivedCategory.Monoidal] [G.mapDerivedCategory.Monoidal]
omit [F.Monoidal] [G.Monoidal] [IsIso adj.unit] [IsIso adj.counit] in
private theorem inverseD_factorsh
    [IsIso (adj.mapHomotopyCategory (.up ℤ)).counit]
    [IsIso adj.mapDerivedCategoryAdjunction.unit]
    [NatTrans.IsMonoidal (adj.mapHomotopyCategory (.up ℤ)).counit]
    [NatTrans.IsMonoidal adj.mapDerivedCategoryAdjunction.unit]
    [NatTrans.IsMonoidal F.mapDerivedCategoryFactorsh.hom] :
    NatTrans.IsMonoidal G.mapDerivedCategoryFactorsh.hom := by
  have hm := rightMateIso_monoidal (adj.mapHomotopyCategory (.up ℤ))
    adj.mapDerivedCategoryAdjunction DerivedCategory.Qh DerivedCategory.Qh
    F.mapDerivedCategoryFactorsh
  have he := rightMateIso_hom_eq (adj.mapHomotopyCategory (.up ℤ))
    adj.mapDerivedCategoryAdjunction DerivedCategory.Qh DerivedCategory.Qh
    F.mapDerivedCategoryFactorsh G.mapDerivedCategoryFactorsh
    adj.mapDerivedCategoryAdjunction_unit_app_fac
  rw [he] at hm
  have : NatTrans.IsMonoidal G.mapDerivedCategoryFactorsh.symm.hom := hm
  exact inferInstanceAs (NatTrans.IsMonoidal G.mapDerivedCategoryFactorsh.symm.inv)
end Descent
end MateConstruction

section ComplexConstruction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal _root_.HomologicalComplex
universe v uA uB
variable {A : Type uA} [Category.{v} A] [Abelian A] [HasColimitsOfSize.{0, 0} A]
  [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A]
  {B : Type uB} [Category.{v} B] [Abelian B] [HasColimitsOfSize.{0, 0} B]
  [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] [F.Monoidal] [G.Monoidal]
  [F.IsEquivalence] [G.IsEquivalence] (adj : F ⊣ G)
  [NatTrans.IsMonoidal adj.counit]

private noncomputable local instance :
    (G.mapHomologicalComplex (.up ℤ) ⋙ F.mapHomologicalComplex (.up ℤ)).LaxMonoidal :=
  Functor.LaxMonoidal.comp _ _

private theorem complexCounit_monoidal :
    NatTrans.IsMonoidal (adj.mapHomologicalComplex (.up ℤ)).counit where
  unit := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [Functor.LaxMonoidal.comp_ε, Functor.LaxMonoidal.id_ε,
      HomologicalComplex.comp_f, assoc]
    change (F.mapCochainComplexεIso).hom.f 0 ≫
      F.map ((G.mapCochainComplexεIso).hom.f 0) ≫ adj.counit.app _ = 𝟙 _
    rw [Functor.mapCochainComplexεIso_hom_f_zero (G := F),
      Functor.mapCochainComplexεIso_hom_f_zero (G := G)]
    simp only [Functor.map_comp, assoc]
    rw [← F.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, id_comp]
    erw [adj.counit.naturality]
    have h := NatTrans.IsMonoidal.unit (τ := adj.counit)
    simp only [Functor.LaxMonoidal.comp_ε, Functor.LaxMonoidal.id_ε] at h
    simp only [assoc] at h ⊢
    rw [reassoc_of% h]
    simp only [CategoryTheory.Functor.id_map, Iso.hom_inv_id]
  tensor K L := by
    simp only [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.id_μ, assoc]
    change (F.mapCochainComplexμIso _ _).hom ≫
      (F.mapHomologicalComplex (.up ℤ)).map (G.mapCochainComplexμIso K L).hom ≫
      (adj.mapHomologicalComplex (.up ℤ)).counit.app (K ⊗ L) =
      ((adj.mapHomologicalComplex (.up ℤ)).counit.app K ⊗ₘ
        (adj.mapHomologicalComplex (.up ℤ)).counit.app L) ≫ 𝟙 _
    rw [Category.comp_id]
    ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    change ιTensorObj _ _ p q n h ≫
      (F.mapCochainComplexμIso _ _).hom.f n ≫
      F.map ((G.mapCochainComplexμIso K L).hom.f n) ≫ adj.counit.app ((K ⊗ L).X n) = _
    erw [Functor.ιTensorObj_mapCochainComplexμIso_hom_f_assoc]
    rw [← F.map_comp_assoc]
    erw [Functor.ιTensorObj_mapCochainComplexμIso_hom_f]
    rw [Functor.map_comp, assoc]
    erw [adj.counit.naturality]
    have ht := NatTrans.IsMonoidal.tensor (τ := adj.counit) (K.X p) (L.X q)
    simp only [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.id_μ, comp_id] at ht
    simp only [assoc] at ht
    erw [reassoc_of% ht]
    simp only [Functor.id_map]
    erw [HomologicalComplex.ι_mapBifunctorMap]
    rw [tensorHom_def, assoc]
    rfl
end ComplexConstruction

section Result
universe v uA uB
variable {A : Type uA} [Category.{v + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{v + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type uB} [Category.{v + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{v + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] [F.Monoidal] [G.Monoidal]
  [F.IsEquivalence] [G.IsEquivalence] (adj : F ⊣ G)
  [IsIso adj.unit] [IsIso adj.counit] [NatTrans.IsMonoidal adj.counit]

/-- Strong derived functors with the canonical localization comparison and monoidal adjunction. -/
structure Data where
  [leftMonoidal : F.mapDerivedCategory.Monoidal]
  [rightMonoidal : G.mapDerivedCategory.Monoidal]
  leftFactors : NatTrans.IsMonoidal F.mapDerivedCategoryFactors.hom
  rightFactors : NatTrans.IsMonoidal G.mapDerivedCategoryFactors.hom
  unit : NatTrans.IsMonoidal adj.mapDerivedCategoryAdjunction.unit
  counit : NatTrans.IsMonoidal adj.mapDerivedCategoryAdjunction.counit

/-- Source: the K-flat derived tensor construction and its localization universal property.
First descend the left equivalence's tensor comparison using K-flat representatives. Its
comparison with the exact localized functor transports this strong structure. Give the right
functor the strong right-adjoint structure. The mate identities for the quotient and localization
comparisons identify their canonical right comparisons with monoidal mates. Composing these
squares gives the prescribed comparisons from complexes. The unit and counit are monoidal by
the right-adjoint construction. (auxiliary; not a blueprint node) -/
theorem nonempty_data : Nonempty (Data adj) := by
  obtain ⟨l⟩ := left_data F
  let := l.homotopyMonoidal
  let := l.derivedMonoidal
  have hfH := l.homotopyFactors
  have hfD := l.derivedFactors
  have huH := hcUnit_iso adj
  have hcH := hcCounit_iso adj
  obtain ⟨rH⟩ := right_data (adj.mapHomotopyCategory (.up ℤ))
  let := rH.monoidal
  have hmH := rH.adjunctionMonoidal
  obtain ⟨rD⟩ := right_data adj.mapDerivedCategoryAdjunction
  let := rD.monoidal
  have hmD := rD.adjunctionMonoidal
  have hcC := complexCounit_iso adj
  have hmC := complexCounit_monoidal adj
  have hgH := inverseHC_factors adj
  have hgD := inverseD_factorsh adj
  exact ⟨{
    leftMonoidal := inferInstance
    rightMonoidal := inferInstance
    leftFactors := derivedFactors_monoidal F
    rightFactors := derivedFactors_monoidal G
    unit := inferInstance
    counit := inferInstance }⟩
end Result
end ExactMonoidalEquivalenceDerived
end CategoryTheory
