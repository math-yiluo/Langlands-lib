import Langlands.Sheaf.Renard.GermSectionSheaf
import Langlands.Sheaf.Renard.BasisLift

/-!
# Canonical maps from original sections to their germ families

The raw and normalized natural transformations use the actual source lifts.
At the joint value universe a separate unit has the identity as its source.
-/

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- The original section itself represents its germ family on the whole basis open. -/
theorem sectionGerms_locallyRepresented (F : RawPresheaf.{u,v} B)
    (U : BasisOpen B) (s : Sections F U) :
    LocallyRepresented F U.obj (fun x => rawGerm F U x.val x.property s) := by
  intro x
  exact ⟨U, x.property, le_rfl, s, fun _ _ => rfl⟩

/-- The canonical additive map sends an original section to its actual original germs. -/
noncomputable def sectionGerms (F : RawPresheaf.{u,v} B) (U : BasisOpen B) :
    Sections F U →+ GermSections F U.obj where
  toFun s := ⟨fun x => rawGerm F U x.val x.property s,
    sectionGerms_locallyRepresented F U s⟩
  map_zero' := by
    apply GermSections.ext
    intro x
    exact rawGerm_zero F U x.val x.property
  map_add' s t := by
    apply GermSections.ext
    intro x
    exact rawGerm_add F U x.val x.property s t

@[simp]
theorem sectionGerms_apply (F : RawPresheaf.{u,v} B) (U : BasisOpen B)
    (s : Sections F U) (x : U.obj) :
    (sectionGerms F U s).val x = rawGerm F U x.val x.property s := rfl

@[simp]
theorem sectionGerms_zero (F : RawPresheaf.{u,v} B) (U : BasisOpen B) :
    sectionGerms F U 0 = 0 :=
  map_zero _

@[simp]
theorem sectionGerms_add (F : RawPresheaf.{u,v} B) (U : BasisOpen B)
    (s t : Sections F U) :
    sectionGerms F U (s + t) = sectionGerms F U s + sectionGerms F U t :=
  map_add _ _ _

@[simp]
theorem sectionGerms_neg (F : RawPresheaf.{u,v} B) (U : BasisOpen B)
    (s : Sections F U) : sectionGerms F U (-s) = -sectionGerms F U s :=
  map_neg _ _

@[simp]
theorem sectionGerms_zero_apply (F : RawPresheaf.{u,v} B) (U : BasisOpen B)
    (x : U.obj) : (sectionGerms F U 0).val x = 0 :=
  rawGerm_zero F U x.val x.property

@[simp]
theorem sectionGerms_add_apply (F : RawPresheaf.{u,v} B) (U : BasisOpen B)
    (s t : Sections F U) (x : U.obj) :
    (sectionGerms F U (s + t)).val x =
      (sectionGerms F U s).val x + (sectionGerms F U t).val x :=
  rawGerm_add F U x.val x.property s t

@[simp]
theorem sectionGerms_neg_apply (F : RawPresheaf.{u,v} B) (U : BasisOpen B)
    (s : Sections F U) (x : U.obj) :
    (sectionGerms F U (-s)).val x = -(sectionGerms F U s).val x :=
  map_neg _ _

/-- Empty-domain uniqueness holds even when the raw source has a nontrivial empty value. -/
theorem sectionGerms_empty (F : RawPresheaf.{u,v} B) (U : BasisOpen B)
    (hU : U.obj = ⊥) (s : Sections F U) : sectionGerms F U s = 0 := by
  apply GermSections.ext
  intro x
  exact False.elim ((le_of_eq hU : U.obj ≤ ⊥) x.property)

/-- Canonical germ families commute with every original basis restriction. -/
theorem sectionGerms_restriction (F : RawPresheaf.{u,v} B)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (s : Sections F V) :
    germRestriction F h (sectionGerms F V s) =
      sectionGerms F U (restriction F h s) := by
  apply GermSections.ext
  intro x
  exact (rawGerm_restriction F h x.val x.property s).symm

/-- Applying the induced stalk-family map gives the germs of the original image section. -/
theorem sectionGerms_map {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : BasisOpen B) (s : Sections F U) :
    germSectionsMap φ U.obj (sectionGerms F U s) =
      sectionGerms G U (φ.app (op U) s) := by
  apply GermSections.ext
  intro x
  exact rawStalkMap_germ φ U x.val x.property s

/-- The raw canonical natural transformation, with the published joint-universe source lift. -/
noncomputable def rawGermSheafLiftUnit (B : OpenBasis X) :
    rawLiftJoint.{u,v} B ⟶
      rawGermSheafFunctor.{u,v} B ⋙ sheafForget.{u,max u v} B ⋙
        presheafInclusion.{u,max u v} B where
  app F :=
    { app U := AddCommGrpCat.ofHom
        ((sectionGerms F U.unop).comp AddEquiv.ulift.toAddMonoidHom)
      naturality U V f := by
        apply AddCommGrpCat.ext
        intro s
        exact (sectionGerms_restriction F f.unop.hom.le s.down).symm }
  naturality F G φ := by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro s
    exact (sectionGerms_map φ U.unop s.down).symm

@[simp]
theorem rawGermSheafLiftUnit_app_app (F : RawPresheaf.{u,v} B) (U : BasisOpen B)
    (t : Sections ((rawLiftJoint B).obj F) U) :
    ((rawGermSheafLiftUnit B).app F).app (op U) t =
      sectionGerms F U t.down := rfl

@[simp]
theorem rawGermSheafLiftUnit_app_app_up (F : RawPresheaf.{u,v} B)
    (U : BasisOpen B) (s : Sections F U) :
    ((rawGermSheafLiftUnit B).app F).app (op U) (ULift.up s) =
      sectionGerms F U s := rfl

@[simp]
theorem rawGermSheafLiftUnit_apply (F : RawPresheaf.{u,v} B) (U : BasisOpen B)
    (t : Sections ((rawLiftJoint B).obj F) U) (x : U.obj) :
    (((rawGermSheafLiftUnit B).app F).app (op U) t).val x =
      rawGerm F U x.val x.property t.down := rfl

theorem rawGermSheafLiftUnit_restriction (F : RawPresheaf.{u,v} B)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj)
    (t : Sections ((rawLiftJoint B).obj F) V) :
    germRestriction F h (((rawGermSheafLiftUnit B).app F).app (op V) t) =
      ((rawGermSheafLiftUnit B).app F).app (op U)
        (restriction ((rawLiftJoint B).obj F) h t) :=
  sectionGerms_restriction F h t.down

theorem rawGermSheafLiftUnit_naturality {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G) :
    (rawLiftJoint B).map φ ≫ (rawGermSheafLiftUnit B).app G =
      (rawGermSheafLiftUnit B).app F ≫
        (rawGermSheafFunctor B ⋙ sheafForget B ⋙ presheafInclusion B).map φ :=
  (rawGermSheafLiftUnit B).naturality φ

theorem rawGermSheafLiftUnit_naturality_apply {F G : RawPresheaf.{u,v} B}
    (φ : F ⟶ G) (U : BasisOpen B) (t : Sections ((rawLiftJoint B).obj F) U) :
    germSectionsMap φ U.obj (((rawGermSheafLiftUnit B).app F).app (op U) t) =
      ((rawGermSheafLiftUnit B).app G).app (op U)
        (((rawLiftJoint B).map φ).app (op U) t) :=
  sectionGerms_map φ U t.down

/-- The normalized canonical natural transformation, with the actual normalized source lift. -/
noncomputable def germSheafLiftUnit (B : OpenBasis X) :
    presheafLiftJoint.{u,v} B ⟶
      germSheafFunctor.{u,v} B ⋙ sheafForget.{u,max u v} B where
  app F := ObjectProperty.homMk ((rawGermSheafLiftUnit B).app F.obj)
  naturality F G φ := by
    apply ObjectProperty.hom_ext
    exact (rawGermSheafLiftUnit B).naturality φ.hom

@[simp]
theorem germSheafLiftUnit_app_hom (F : Presheaf.{u,v} B) :
    ((germSheafLiftUnit B).app F).hom = (rawGermSheafLiftUnit B).app F.obj := rfl

/-- Erasing normalization agrees with the raw unit through the published lift comparison. -/
theorem germSheafLiftUnit_erasure (B : OpenBasis X) :
    Functor.whiskerRight (germSheafLiftUnit.{u,v} B) (presheafInclusion.{u,max u v} B) =
      (presheafLiftCompInclusionIso.{u,v,u} B).hom ≫
        Functor.whiskerLeft (presheafInclusion.{u,v} B) (rawGermSheafLiftUnit B) := by
  apply NatTrans.ext
  funext F
  apply NatTrans.ext
  funext U
  rfl

@[simp]
theorem germSheafLiftUnit_app_app (F : Presheaf.{u,v} B) (U : BasisOpen B)
    (t : Sections ((presheafLiftJoint B).obj F).obj U) :
    ((germSheafLiftUnit B).app F).hom.app (op U) t =
      sectionGerms F.obj U t.down := rfl

@[simp]
theorem germSheafLiftUnit_app_app_up (F : Presheaf.{u,v} B) (U : BasisOpen B)
    (s : Sections F.obj U) :
    ((germSheafLiftUnit B).app F).hom.app (op U) (ULift.up s) =
      sectionGerms F.obj U s := rfl

@[simp]
theorem germSheafLiftUnit_apply (F : Presheaf.{u,v} B) (U : BasisOpen B)
    (s : Sections F.obj U) (x : U.obj) :
    (((germSheafLiftUnit B).app F).hom.app (op U) (ULift.up s)).val x =
      rawGerm F.obj U x.val x.property s := rfl

theorem germSheafLiftUnit_restriction (F : Presheaf.{u,v} B)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj)
    (t : Sections ((presheafLiftJoint B).obj F).obj V) :
    germRestriction F.obj h (((germSheafLiftUnit B).app F).hom.app (op V) t) =
      ((germSheafLiftUnit B).app F).hom.app (op U)
        (restriction ((presheafLiftJoint B).obj F).obj h t) :=
  sectionGerms_restriction F.obj h t.down

theorem germSheafLiftUnit_naturality {F G : Presheaf.{u,v} B} (φ : F ⟶ G) :
    (presheafLiftJoint B).map φ ≫ (germSheafLiftUnit B).app G =
      (germSheafLiftUnit B).app F ≫ (germSheafFunctor B ⋙ sheafForget B).map φ :=
  (germSheafLiftUnit B).naturality φ

theorem germSheafLiftUnit_naturality_apply {F G : Presheaf.{u,v} B}
    (φ : F ⟶ G) (U : BasisOpen B)
    (t : Sections ((presheafLiftJoint B).obj F).obj U) :
    germSectionsMap φ.hom U.obj (((germSheafLiftUnit B).app F).hom.app (op U) t) =
      ((germSheafLiftUnit B).app G).hom.app (op U)
        (((presheafLiftJoint B).map φ).hom.app (op U) t) :=
  sectionGerms_map φ.hom U t.down

/-- At the joint value universe the canonical map has the identity functor as source. -/
noncomputable def germSheafUnit (B : OpenBasis X) :
    𝟭 (Presheaf.{u,max u v} B) ⟶
      germSheafFunctor.{u,max u v} B ⋙ sheafForget.{u,max u v} B where
  app F := ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (sectionGerms F.obj U.unop)
      naturality U V f := by
        apply AddCommGrpCat.ext
        intro s
        exact (sectionGerms_restriction F.obj f.unop.hom.le s).symm }
  naturality F G φ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro s
    exact (sectionGerms_map φ.hom U.unop s).symm

@[simp]
theorem germSheafUnit_app_app (F : Presheaf.{u,max u v} B) (U : BasisOpen B)
    (s : Sections F.obj U) :
    ((germSheafUnit.{u,v} B).app F).hom.app (op U) s = sectionGerms F.obj U s := rfl

@[simp]
theorem germSheafUnit_apply (F : Presheaf.{u,max u v} B) (U : BasisOpen B)
    (s : Sections F.obj U) (x : U.obj) :
    (((germSheafUnit.{u,v} B).app F).hom.app (op U) s).val x =
      rawGerm F.obj U x.val x.property s := rfl

theorem germSheafUnit_restriction (F : Presheaf.{u,max u v} B)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (s : Sections F.obj V) :
    germRestriction F.obj h (((germSheafUnit.{u,v} B).app F).hom.app (op V) s) =
      ((germSheafUnit.{u,v} B).app F).hom.app (op U) (restriction F.obj h s) :=
  sectionGerms_restriction F.obj h s

theorem germSheafUnit_naturality {F G : Presheaf.{u,max u v} B} (φ : F ⟶ G) :
    φ ≫ (germSheafUnit.{u,v} B).app G =
      (germSheafUnit.{u,v} B).app F ≫ (germSheafFunctor B ⋙ sheafForget B).map φ :=
  (germSheafUnit.{u,v} B).naturality φ

theorem germSheafUnit_naturality_apply {F G : Presheaf.{u,max u v} B}
    (φ : F ⟶ G) (U : BasisOpen B) (s : Sections F.obj U) :
    germSectionsMap φ.hom U.obj (((germSheafUnit.{u,v} B).app F).hom.app (op U) s) =
      ((germSheafUnit.{u,v} B).app G).hom.app (op U) (φ.hom.app (op U) s) :=
  sectionGerms_map φ.hom U s

/-- Precomposing the lifted unit with the published up isomorphism recovers the direct unit. -/
theorem germSheafUnit_eq_relift (B : OpenBasis X) :
    (presheafReliftJoint.{u,v} B).inv ≫ germSheafLiftUnit.{u,max u v} B =
      germSheafUnit.{u,v} B := by
  apply NatTrans.ext
  funext F
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  rfl

end Langlands.Sheaf.Renard
