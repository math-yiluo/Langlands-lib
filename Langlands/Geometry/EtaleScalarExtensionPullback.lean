import Langlands.Geometry.EtaleScalarExtension
import Langlands.Geometry.EtaleRestrictionRightAdjoint

/-!
# Sheafified scalar extension and etale restriction
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry EtalePullback
open scoped ChangeOfRings

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]

/-- Sheafified scalar extension commutes with restriction along an etale scheme map. -/
def sheafExtendScalarsPullbackIso :
    sheafExtendScalars φ X ⋙ restriction f (ModuleCat.{u} S) ≅
      restriction f (ModuleCat.{u} R) ⋙ sheafExtendScalars φ Y :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} R) ⋙
      (Functor.whiskeringRight X.Etaleᵒᵖ (ModuleCat.{u} R) (ModuleCat.{u} S)).obj
        (ModuleCat.extendScalars φ))
    ((siteMap f).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u} S)
      Y.smallEtaleTopology X.smallEtaleTopology).symm

/-- The comparison identifies the two canonical maps out of the tensor presheaf. -/
theorem tensorToSheafExtension_pullback (F : EtaleDerivedSections.ModuleSheaf X R) :
    Functor.whiskerLeft (siteMap f).op (tensorToSheafExtension φ X F) ≫
      ((sheafExtendScalarsPullbackIso φ f).hom.app F).hom =
        tensorToSheafExtension φ Y ((restriction f (ModuleCat.{u} R)).obj F) := by
  have h := (siteMap f).toSheafify_pullbackSheafificationCompatibility
    (ModuleCat.{u} S) Y.smallEtaleTopology X.smallEtaleTopology
    (F.obj ⋙ ModuleCat.extendScalars φ)
  change Functor.whiskerLeft (siteMap f).op (toSheafify X.smallEtaleTopology _) ≫
    (((siteMap f).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u} S)
      Y.smallEtaleTopology X.smallEtaleTopology).inv.app _).hom = _
  rw [← h, Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app]
  rfl

/-- Restricting the coefficient unit agrees with the unit after restriction. -/
theorem sheafExtensionUnit_pullback (F : EtaleDerivedSections.ModuleSheaf X R) :
    (restriction f (ModuleCat.{u} R)).map ((sheafExtensionUnit φ X).app F) ≫
      (sheafRestrictScalars φ Y).map ((sheafExtendScalarsPullbackIso φ f).hom.app F) =
        (sheafExtensionUnit φ Y).app ((restriction f (ModuleCat.{u} R)).obj F) := by
  apply Sheaf.hom_ext
  ext U m
  change (((sheafExtendScalarsPullbackIso φ f).hom.app F).hom.app U)
      ((((sheafExtensionUnit φ X).app F).hom.app ((siteMap f).op.obj U)) m) =
    (((sheafExtensionUnit φ Y).app ((restriction f (ModuleCat.{u} R)).obj F)).hom.app U) m
  simp only [sheafExtensionUnit_app_apply]
  exact congrArg (fun a => (a.app U) ((1 : S) ⊗ₜ[R,φ] m))
    (tensorToSheafExtension_pullback φ f F)

/-- The inverse comparison is the sheafification lift of the restricted tensor map. -/
theorem tensorToSheafExtension_pullback_inv (F : EtaleDerivedSections.ModuleSheaf X R) :
    tensorToSheafExtension φ Y ((restriction f (ModuleCat.{u} R)).obj F) ≫
      ((sheafExtendScalarsPullbackIso φ f).inv.app F).hom =
        Functor.whiskerLeft (siteMap f).op (tensorToSheafExtension φ X F) :=
  (siteMap f).toSheafify_pullbackSheafificationCompatibility
    (ModuleCat.{u} S) Y.smallEtaleTopology X.smallEtaleTopology
    (F.obj ⋙ ModuleCat.extendScalars φ)

/-- Morphisms out of restricted scalar extension are determined on the tensor presheaf. -/
theorem sheafExtensionPullback_hom_ext (F : EtaleDerivedSections.ModuleSheaf X R)
    {E : EtaleDerivedSections.ModuleSheaf Y S}
    (a b : (restriction f (ModuleCat.{u} S)).obj ((sheafExtendScalars φ X).obj F) ⟶ E)
    (h : Functor.whiskerLeft (siteMap f).op (tensorToSheafExtension φ X F) ≫ a.hom =
      Functor.whiskerLeft (siteMap f).op (tensorToSheafExtension φ X F) ≫ b.hom) : a = b := by
  have h' : (sheafExtendScalarsPullbackIso φ f).inv.app F ≫ a =
      (sheafExtendScalarsPullbackIso φ f).inv.app F ≫ b := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext Y.smallEtaleTopology _ _ E.property
    change tensorToSheafExtension φ Y ((restriction f (ModuleCat.{u} R)).obj F) ≫
        ((sheafExtendScalarsPullbackIso φ f).inv.app F).hom ≫ a.hom =
      tensorToSheafExtension φ Y ((restriction f (ModuleCat.{u} R)).obj F) ≫
        ((sheafExtendScalarsPullbackIso φ f).inv.app F).hom ≫ b.hom
    simpa only [← Category.assoc, tensorToSheafExtension_pullback_inv] using h
  have h'' := congrArg (fun k => (sheafExtendScalarsPullbackIso φ f).hom.app F ≫ k) h'
  simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using h''

/-- Tensor-to-extension maps are natural in the coefficient sheaf. -/
theorem tensorToSheafExtension_naturality {F F' : EtaleDerivedSections.ModuleSheaf X R}
    (a : F ⟶ F') :
    tensorToSheafExtension φ X F ≫ ((sheafExtendScalars φ X).map a).hom =
      Functor.whiskerRight a.hom (ModuleCat.extendScalars φ) ≫
        tensorToSheafExtension φ X F' :=
  (toSheafify_naturality X.smallEtaleTopology _).symm

/-- The pullback comparison respects the geometric identity comparison. -/
theorem sheafExtendScalarsPullbackIso_id (F : EtaleDerivedSections.ModuleSheaf X R) :
    (sheafExtendScalarsPullbackIso φ (𝟙 X)).hom.app F ≫
      (sheafExtendScalars φ X).map ((restrictionId (ModuleCat.{u} R)).hom.app F) =
        (restrictionId (ModuleCat.{u} S)).hom.app ((sheafExtendScalars φ X).obj F) := by
  apply sheafExtensionPullback_hom_ext φ (𝟙 X) F
  change Functor.whiskerLeft (siteMap (𝟙 X)).op (tensorToSheafExtension φ X F) ≫
      ((sheafExtendScalarsPullbackIso φ (𝟙 X)).hom.app F).hom ≫
        ((sheafExtendScalars φ X).map ((restrictionId (ModuleCat.{u} R)).hom.app F)).hom = _
  rw [← Category.assoc, tensorToSheafExtension_pullback, tensorToSheafExtension_naturality]
  apply NatTrans.ext
  funext U
  dsimp [restrictionId]
  simp only [Category.comp_id]
  exact (tensorToSheafExtension φ X F).naturality _

/-- Tensor sheafification respects the site comparison for a composite geometric map. -/
theorem tensorToSheafExtension_restrictionComp_inv {Z : Scheme.{u}} (g : Z ⟶ Y) [Etale g]
    (F : EtaleDerivedSections.ModuleSheaf X R) :
    Functor.whiskerLeft (siteMap (g ≫ f)).op (tensorToSheafExtension φ X F) ≫
      ((restrictionComp f (ModuleCat.{u} S) g).inv.app ((sheafExtendScalars φ X).obj F)).hom =
    Functor.whiskerRight ((restrictionComp f (ModuleCat.{u} R) g).inv.app F).hom
        (ModuleCat.extendScalars φ) ≫
      Functor.whiskerLeft (siteMap g).op
        (Functor.whiskerLeft (siteMap f).op (tensorToSheafExtension φ X F)) := by
  apply NatTrans.ext
  funext U
  dsimp [restrictionComp]
  exact ((tensorToSheafExtension φ X F).naturality _).symm

/-- The pullback comparisons respect composition of etale maps. -/
theorem sheafExtendScalarsPullbackIso_comp {Z : Scheme.{u}} (g : Z ⟶ Y) [Etale g]
    (F : EtaleDerivedSections.ModuleSheaf X R) :
    (sheafExtendScalarsPullbackIso φ (g ≫ f)).hom.app F ≫
      (sheafExtendScalars φ Z).map ((restrictionComp f (ModuleCat.{u} R) g).inv.app F) =
    (restrictionComp f (ModuleCat.{u} S) g).inv.app ((sheafExtendScalars φ X).obj F) ≫
      (restriction g (ModuleCat.{u} S)).map ((sheafExtendScalarsPullbackIso φ f).hom.app F) ≫
        (sheafExtendScalarsPullbackIso φ g).hom.app ((restriction f (ModuleCat.{u} R)).obj F) := by
  apply sheafExtensionPullback_hom_ext φ (g ≫ f) F
  change Functor.whiskerLeft (siteMap (g ≫ f)).op (tensorToSheafExtension φ X F) ≫
      ((sheafExtendScalarsPullbackIso φ (g ≫ f)).hom.app F).hom ≫
        ((sheafExtendScalars φ Z).map ((restrictionComp f (ModuleCat.{u} R) g).inv.app F)).hom =
    Functor.whiskerLeft (siteMap (g ≫ f)).op (tensorToSheafExtension φ X F) ≫
      ((restrictionComp f (ModuleCat.{u} S) g).inv.app ((sheafExtendScalars φ X).obj F)).hom ≫
        Functor.whiskerLeft (siteMap g).op ((sheafExtendScalarsPullbackIso φ f).hom.app F).hom ≫
          ((sheafExtendScalarsPullbackIso φ g).hom.app _).hom
  rw [← Category.assoc, tensorToSheafExtension_pullback, tensorToSheafExtension_naturality]
  rw [← Category.assoc, tensorToSheafExtension_restrictionComp_inv]
  rw [Category.assoc, ← Functor.whiskerLeft_comp_assoc, tensorToSheafExtension_pullback,
    tensorToSheafExtension_pullback]
  rfl

end Langlands.Geometry.EtaleCohomologyAction
