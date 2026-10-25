import Langlands.Geometry.EtaleScalarExtensionPullback

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry EtalePullback
open Langlands.Cohomology

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable {X : Scheme.{u}} {G : Type w} [Group G] (ρ : G →* (Aut X)ᵐᵒᵖ)

/-- The geometric structure map on the sheafified scalar extension. -/
def scalarExtensionAct (F : EquivariantSheaf R ρ) (g : G) :
    (translateBy S ρ g).obj ((sheafExtendScalars φ X).obj F.obj) ⟶
      (sheafExtendScalars φ X).obj F.obj :=
  (sheafExtendScalarsPullbackIso φ (aut ρ g).hom).hom.app F.obj ≫
    (sheafExtendScalars φ X).map (F.act g)

/-- The extended action restricts on the tensor presheaf to the tensor of the original action. -/
theorem tensorToSheafExtension_act (F : EquivariantSheaf R ρ) (g : G) :
    Functor.whiskerLeft (siteMap (aut ρ g).hom).op (tensorToSheafExtension φ X F.obj) ≫
      (scalarExtensionAct φ ρ F g).hom =
    Functor.whiskerRight (F.act g).hom (ModuleCat.extendScalars φ) ≫
      tensorToSheafExtension φ X F.obj := by
  change _ ≫ ((sheafExtendScalarsPullbackIso φ (aut ρ g).hom).hom.app F.obj).hom ≫ _ = _
  rw [← Category.assoc, tensorToSheafExtension_pullback, tensorToSheafExtension_naturality]

/-- The tensor map is natural across the translation unit constraint. -/
theorem tensorToSheafExtension_oneIso (F : EtaleDerivedSections.ModuleSheaf X R) :
    Functor.whiskerLeft (siteMap (aut ρ 1).hom).op (tensorToSheafExtension φ X F) ≫
      ((oneIso S ρ).hom.app ((sheafExtendScalars φ X).obj F)).hom =
    Functor.whiskerRight ((oneIso R ρ).hom.app F).hom (ModuleCat.extendScalars φ) ≫
      tensorToSheafExtension φ X F := by
  apply NatTrans.ext
  funext U
  dsimp [oneIso, EtaleAutomorphism.translateCongr, EtaleAutomorphism.translateId]
  simp only [Category.comp_id, ← Functor.map_comp]
  exact ((tensorToSheafExtension φ X F).naturality _).symm

/-- The tensor map is natural across the inverse translation composition constraint. -/
theorem tensorToSheafExtension_compIso_inv (F : EtaleDerivedSections.ModuleSheaf X R)
    (g h : G) :
    Functor.whiskerLeft (siteMap (aut ρ (g * h)).hom).op (tensorToSheafExtension φ X F) ≫
      ((compIso S ρ g h).inv.app ((sheafExtendScalars φ X).obj F)).hom =
    Functor.whiskerRight ((compIso R ρ g h).inv.app F).hom (ModuleCat.extendScalars φ) ≫
      Functor.whiskerLeft (siteMap (aut ρ g).hom).op
        (Functor.whiskerLeft (siteMap (aut ρ h).hom).op (tensorToSheafExtension φ X F)) := by
  apply NatTrans.ext
  funext U
  dsimp [compIso, EtaleAutomorphism.translateCongr, EtaleAutomorphism.translateComp]
  simp only [← Functor.map_comp]
  exact ((tensorToSheafExtension φ X F).naturality _).symm

/-- Scalar extension respects the unit constraint of geometric equivariance. -/
theorem scalarExtensionAct_one (F : EquivariantSheaf R ρ) :
    scalarExtensionAct φ ρ F 1 =
      (oneIso S ρ).hom.app ((sheafExtendScalars φ X).obj F.obj) := by
  apply sheafExtensionPullback_hom_ext φ (aut ρ 1).hom F.obj
  rw [tensorToSheafExtension_act, tensorToSheafExtension_oneIso, F.act_one]
  rfl

/-- Scalar extension respects the multiplication constraint of geometric equivariance. -/
theorem scalarExtensionAct_mul (F : EquivariantSheaf R ρ) (g h : G) :
    scalarExtensionAct φ ρ F (g * h) =
      (compIso S ρ g h).inv.app ((sheafExtendScalars φ X).obj F.obj) ≫
        (translateBy S ρ g).map (scalarExtensionAct φ ρ F h) ≫
          scalarExtensionAct φ ρ F g := by
  apply sheafExtensionPullback_hom_ext φ (aut ρ (g * h)).hom F.obj
  change _ =
    Functor.whiskerLeft (siteMap (aut ρ (g * h)).hom).op
        (tensorToSheafExtension φ X F.obj) ≫
      ((compIso S ρ g h).inv.app ((sheafExtendScalars φ X).obj F.obj)).hom ≫
        Functor.whiskerLeft (siteMap (aut ρ g).hom).op
          (scalarExtensionAct φ ρ F h).hom ≫ (scalarExtensionAct φ ρ F g).hom
  rw [tensorToSheafExtension_act, ← Category.assoc, tensorToSheafExtension_compIso_inv]
  rw [Category.assoc, ← Functor.whiskerLeft_comp_assoc, tensorToSheafExtension_act]
  rw [Functor.whiskerLeft_comp, Category.assoc, tensorToSheafExtension_act, F.act_mul]
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.whiskerRight_comp,
    Category.assoc]
  rfl

/-- The actual scalar extension equipped with its induced geometric action. -/
def scalarExtensionObj (F : EquivariantSheaf R ρ) : EquivariantSheaf S ρ where
  obj := (sheafExtendScalars φ X).obj F.obj
  act := scalarExtensionAct φ ρ F
  act_one := scalarExtensionAct_one φ ρ F
  act_mul := scalarExtensionAct_mul φ ρ F

/-- Scalar extension carries equivariant morphisms to equivariant morphisms. -/
theorem scalarExtensionAct_naturality {F E : EquivariantSheaf R ρ} (a : F ⟶ E)
    (g : G) :
    scalarExtensionAct φ ρ F g ≫ (sheafExtendScalars φ X).map a.hom =
      (translateBy S ρ g).map ((sheafExtendScalars φ X).map a.hom) ≫
        scalarExtensionAct φ ρ E g := by
  dsimp only [scalarExtensionAct]
  rw [Category.assoc, ← Functor.map_comp, a.comm, Functor.map_comp, ← Category.assoc]
  have h := (sheafExtendScalarsPullbackIso φ (aut ρ g).hom).hom.naturality a.hom
  dsimp only [Functor.comp_map] at h
  exact (congrArg (fun k => k ≫ (sheafExtendScalars φ X).map (E.act g)) h.symm).trans
    (Category.assoc _ _ _)

/-- Sheafified scalar extension is functorial on equivariant coefficients. -/
def scalarExtensionFunctor : EquivariantSheaf R ρ ⥤ EquivariantSheaf S ρ where
  obj := scalarExtensionObj φ ρ
  map a := ⟨(sheafExtendScalars φ X).map a.hom, scalarExtensionAct_naturality φ ρ a⟩
  map_id F := by
    apply TranslationAction.Equivariant.Hom.ext
    exact (sheafExtendScalars φ X).map_id F.obj
  map_comp a b := by
    apply TranslationAction.Equivariant.Hom.ext
    exact (sheafExtendScalars φ X).map_comp a.hom b.hom

/-- Forgetting the action recovers the ordinary sheafified scalar extension. -/
def scalarExtensionForgetIso :
    scalarExtensionFunctor φ ρ ⋙ TranslationAction.Equivariant.forget ≅
      TranslationAction.Equivariant.forget ⋙ sheafExtendScalars φ X :=
  Iso.refl _

/-- The ordinary extension unit commutes with the geometric structure maps. -/
theorem scalarExtensionUnit_comm (F : EquivariantSheaf R ρ) (g : G) :
    F.act g ≫ (sheafExtensionUnit φ X).app F.obj =
      (translateBy R ρ g).map ((sheafExtensionUnit φ X).app F.obj) ≫
        (scalarRestrictionObj φ ρ (scalarExtensionObj φ ρ F)).act g := by
  change F.act g ≫ (sheafExtensionUnit φ X).app F.obj =
    (restriction (aut ρ g).hom (ModuleCat.{u} R)).map
        ((sheafExtensionUnit φ X).app F.obj) ≫
      (sheafRestrictScalars φ X).map
        ((sheafExtendScalarsPullbackIso φ (aut ρ g).hom).hom.app F.obj ≫
          (sheafExtendScalars φ X).map (F.act g))
  rw [Functor.map_comp, ← Category.assoc, sheafExtensionUnit_pullback]
  exact (sheafExtensionUnit φ X).naturality (F.act g)

/-- The ordinary extension counit commutes with the geometric structure maps. -/
theorem scalarExtensionCounit_comm (E : EquivariantSheaf S ρ) (g : G) :
    (scalarExtensionObj φ ρ (scalarRestrictionObj φ ρ E)).act g ≫
        (sheafExtensionCounit φ X).app E.obj =
      (translateBy S ρ g).map ((sheafExtensionCounit φ X).app E.obj) ≫ E.act g := by
  apply sheafExtensionPullback_hom_ext φ (aut ρ g).hom
    ((sheafRestrictScalars φ X).obj E.obj)
  change Functor.whiskerLeft (siteMap (aut ρ g).hom).op
        (tensorToSheafExtension φ X ((sheafRestrictScalars φ X).obj E.obj)) ≫
      (scalarExtensionAct φ ρ (scalarRestrictionObj φ ρ E) g).hom ≫
        ((sheafExtensionCounit φ X).app E.obj).hom =
    Functor.whiskerLeft (siteMap (aut ρ g).hom).op
        (tensorToSheafExtension φ X ((sheafRestrictScalars φ X).obj E.obj)) ≫
      Functor.whiskerLeft (siteMap (aut ρ g).hom).op
        ((sheafExtensionCounit φ X).app E.obj).hom ≫ (E.act g).hom
  rw [← Category.assoc]
  erw [tensorToSheafExtension_act φ ρ (scalarRestrictionObj φ ρ E) g]
  dsimp only [scalarRestrictionObj]
  rw [Category.assoc,
    tensorToSheafExtension_counit, ← Functor.whiskerLeft_comp_assoc,
    tensorToSheafExtension_counit]
  apply NatTrans.ext
  funext U
  exact (ModuleCat.extendRestrictScalarsAdj φ).counit.naturality ((E.act g).hom.app U)

/-- The scalar-extension unit as a natural transformation of equivariant sheaves. -/
def scalarExtensionUnit :
    𝟭 (EquivariantSheaf R ρ) ⟶
      scalarExtensionFunctor φ ρ ⋙ scalarRestrictionFunctor φ ρ where
  app F := ⟨(sheafExtensionUnit φ X).app F.obj, scalarExtensionUnit_comm φ ρ F⟩
  naturality {F E} a := by
    apply TranslationAction.Equivariant.Hom.ext
    exact (sheafExtensionUnit φ X).naturality a.hom

/-- The scalar-extension counit as a natural transformation of equivariant sheaves. -/
def scalarExtensionCounit :
    scalarRestrictionFunctor φ ρ ⋙ scalarExtensionFunctor φ ρ ⟶
      𝟭 (EquivariantSheaf S ρ) where
  app E := ⟨(sheafExtensionCounit φ X).app E.obj, scalarExtensionCounit_comm φ ρ E⟩
  naturality {F E} a := by
    apply TranslationAction.Equivariant.Hom.ext
    exact (sheafExtensionCounit φ X).naturality a.hom

/-- Sheafified scalar extension is left adjoint to equivariant scalar restriction. -/
def scalarExtensionRestrictionAdj :
    scalarExtensionFunctor φ ρ ⊣ scalarRestrictionFunctor φ ρ where
  unit := scalarExtensionUnit φ ρ
  counit := scalarExtensionCounit φ ρ
  left_triangle_components F := by
    apply TranslationAction.Equivariant.Hom.ext
    exact (sheafExtendRestrictScalarsAdj φ X).left_triangle_components F.obj
  right_triangle_components E := by
    apply TranslationAction.Equivariant.Hom.ext
    exact (sheafExtendRestrictScalarsAdj φ X).right_triangle_components E.obj

instance : (scalarExtensionFunctor φ ρ).IsLeftAdjoint :=
  (scalarExtensionRestrictionAdj φ ρ).isLeftAdjoint

/-- The universal correspondence restricted to equivariant morphisms. -/
def scalarExtensionHomEquiv (F : EquivariantSheaf R ρ) (E : EquivariantSheaf S ρ) :
    ((scalarExtensionFunctor φ ρ).obj F ⟶ E) ≃
      (F ⟶ (scalarRestrictionFunctor φ ρ).obj E) :=
  (scalarExtensionRestrictionAdj φ ρ).homEquiv F E

/-- The equivariant correspondence has the ordinary correspondence as its underlying map. -/
theorem scalarExtensionHomEquiv_hom (F : EquivariantSheaf R ρ)
    (E : EquivariantSheaf S ρ) (a : (scalarExtensionFunctor φ ρ).obj F ⟶ E) :
    (scalarExtensionHomEquiv φ ρ F E a).hom =
      sheafExtensionHomEquiv φ X F.obj E.obj a.hom := rfl

/-- The equivariant lift is the ordinary universal sheafified tensor lift. -/
theorem scalarExtensionHomEquiv_symm_hom (F : EquivariantSheaf R ρ)
    (E : EquivariantSheaf S ρ) (a : F ⟶ (scalarRestrictionFunctor φ ρ).obj E) :
    ((scalarExtensionHomEquiv φ ρ F E).symm a).hom =
      sheafExtensionLift φ X a.hom := rfl

/-- Extend an equivariant coefficient morphism through sheafified tensor extension. -/
def scalarExtensionLift {F : EquivariantSheaf R ρ} {E : EquivariantSheaf S ρ}
    (a : F ⟶ (scalarRestrictionFunctor φ ρ).obj E) :
    (scalarExtensionFunctor φ ρ).obj F ⟶ E :=
  (scalarExtensionHomEquiv φ ρ F E).symm a

/-- The equivariant lift factors the original morphism through the unit. -/
@[simp] theorem scalarExtensionUnit_lift {F : EquivariantSheaf R ρ}
    {E : EquivariantSheaf S ρ} (a : F ⟶ (scalarRestrictionFunctor φ ρ).obj E) :
    (scalarExtensionUnit φ ρ).app F ≫
      (scalarRestrictionFunctor φ ρ).map (scalarExtensionLift φ ρ a) = a := by
  apply TranslationAction.Equivariant.Hom.ext
  exact sheafExtensionUnit_lift φ X a.hom

/-- An equivariant morphism satisfying the unit equation is the constructed lift. -/
theorem scalarExtensionLift_unique {F : EquivariantSheaf R ρ}
    {E : EquivariantSheaf S ρ} (a : F ⟶ (scalarRestrictionFunctor φ ρ).obj E)
    (b : (scalarExtensionFunctor φ ρ).obj F ⟶ E)
    (h : (scalarExtensionUnit φ ρ).app F ≫ (scalarRestrictionFunctor φ ρ).map b = a) :
    b = scalarExtensionLift φ ρ a := by
  apply TranslationAction.Equivariant.Hom.ext
  exact sheafExtensionLift_unique φ X a.hom b.hom
    (congrArg TranslationAction.Equivariant.Hom.hom h)

/-- Universal equivariant extension is natural in the source coefficient sheaf. -/
theorem scalarExtensionLift_precomp {F F' : EquivariantSheaf R ρ}
    {E : EquivariantSheaf S ρ} (b : F' ⟶ F)
    (a : F ⟶ (scalarRestrictionFunctor φ ρ).obj E) :
    scalarExtensionLift φ ρ (b ≫ a) =
      (scalarExtensionFunctor φ ρ).map b ≫ scalarExtensionLift φ ρ a :=
  (scalarExtensionRestrictionAdj φ ρ).homEquiv_naturality_left_symm b a

/-- Universal equivariant extension is natural in the target coefficient sheaf. -/
theorem scalarExtensionLift_postcomp {F : EquivariantSheaf R ρ}
    {E E' : EquivariantSheaf S ρ} (a : F ⟶ (scalarRestrictionFunctor φ ρ).obj E)
    (b : E ⟶ E') :
    scalarExtensionLift φ ρ (a ≫ (scalarRestrictionFunctor φ ρ).map b) =
      scalarExtensionLift φ ρ a ≫ b :=
  (scalarExtensionRestrictionAdj φ ρ).homEquiv_naturality_right_symm a b

end Langlands.Geometry.EtaleCohomologyAction
