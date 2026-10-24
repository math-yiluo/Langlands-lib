import Langlands.Geometry.EtaleScalarRestriction
import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Sheafified tensor extension on the small etale site
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open scoped ChangeOfRings

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable (X : Scheme.{u})

/-- Tensor the section modules and sheafify on the actual small-etale site. -/
def sheafExtendScalars :
    EtaleDerivedSections.ModuleSheaf X R ⥤ EtaleDerivedSections.ModuleSheaf X S :=
  Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.extendScalars.{u, u, u} φ)

/-- Sheafified tensor extension is left adjoint to the existing scalar restriction. -/
def sheafExtendRestrictScalarsAdj :
    sheafExtendScalars φ X ⊣ sheafRestrictScalars φ X :=
  Sheaf.adjunction X.smallEtaleTopology (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ)

instance : (sheafExtendScalars φ X).IsLeftAdjoint :=
  (sheafExtendRestrictScalarsAdj φ X).isLeftAdjoint

/-- The sheafification map from the tensor presheaf to scalar extension. -/
def tensorToSheafExtension (F : EtaleDerivedSections.ModuleSheaf X R) :
    F.obj ⋙ ModuleCat.extendScalars.{u, u, u} φ ⟶
      ((sheafExtendScalars φ X).obj F).obj :=
  toSheafify X.smallEtaleTopology _

/-- The canonical coefficient map into the restricted scalar extension. -/
def sheafExtensionUnit :
    𝟭 (EtaleDerivedSections.ModuleSheaf X R) ⟶
      sheafExtendScalars φ X ⋙ sheafRestrictScalars φ X :=
  (sheafExtendRestrictScalarsAdj φ X).unit

/-- The canonical evaluation from extension of restricted coefficients. -/
def sheafExtensionCounit :
    sheafRestrictScalars φ X ⋙ sheafExtendScalars φ X ⟶
      𝟭 (EtaleDerivedSections.ModuleSheaf X S) :=
  (sheafExtendRestrictScalarsAdj φ X).counit

/-- Before sheafification, the unit is the sectionwise map `m ↦ 1 ⊗ m`. -/
theorem sheafExtensionUnit_hom (F : EtaleDerivedSections.ModuleSheaf X R) :
    ((sheafExtensionUnit φ X).app F).hom =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).whiskerRight X.Etaleᵒᵖ).unit.app F.obj ≫
        Functor.whiskerRight (tensorToSheafExtension φ X F) (ModuleCat.restrictScalars φ) :=
  Sheaf.adjunction_unit_app_hom (D := ModuleCat.{u} S) (E := ModuleCat.{u} R) X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ) F

/-- A section enters the extension by the sheafification image of `1 ⊗ m`. -/
theorem sheafExtensionUnit_app_apply (F : EtaleDerivedSections.ModuleSheaf X R)
    (U : X.Etaleᵒᵖ) (m : F.obj.obj U) :
    (((sheafExtensionUnit φ X).app F).hom.app U) m =
      (tensorToSheafExtension φ X F).app U ((1 : S) ⊗ₜ[R,φ] m) := by
  rw [sheafExtensionUnit_hom]
  rfl

/-- The counit extends the sectionwise tensor evaluation to the sheafification. -/
theorem sheafExtensionCounit_hom (E : EtaleDerivedSections.ModuleSheaf X S) :
    ((sheafExtensionCounit φ X).app E).hom =
      sheafifyLift X.smallEtaleTopology
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).whiskerRight X.Etaleᵒᵖ).counit.app E.obj)
        E.property :=
  Sheaf.adjunction_counit_app_hom (D := ModuleCat.{u} S) (E := ModuleCat.{u} R) X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ) E

/-- Evaluation on the sheafified tensor presheaf recovers the module counit. -/
theorem tensorToSheafExtension_counit (E : EtaleDerivedSections.ModuleSheaf X S) :
    tensorToSheafExtension φ X ((sheafRestrictScalars φ X).obj E) ≫
      ((sheafExtensionCounit φ X).app E).hom =
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).whiskerRight X.Etaleᵒᵖ).counit.app
          E.obj := by
  rw [sheafExtensionCounit_hom]
  exact toSheafify_sheafifyLift X.smallEtaleTopology _ E.property

/-- The counit takes the sheafification image of `1 ⊗ m` back to `m`. -/
theorem sheafExtensionCounit_app_one_tmul (E : EtaleDerivedSections.ModuleSheaf X S)
    (U : X.Etaleᵒᵖ) (m : E.obj.obj U) :
    (((sheafExtensionCounit φ X).app E).hom.app U)
      ((tensorToSheafExtension φ X ((sheafRestrictScalars φ X).obj E)).app U
        ((1 : S) ⊗ₜ[R,φ] (m : ((sheafRestrictScalars φ X).obj E).obj.obj U))) = m := by
  have h := congrArg (fun α => α.app U)
    (tensorToSheafExtension_counit φ X E)
  have hm := congrArg (fun f => f ((1 : S) ⊗ₜ[R,φ]
    (m : ((sheafRestrictScalars φ X).obj E).obj.obj U))) h
  exact hm.trans (ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul φ
    (E.obj.obj U) m)

/-- Sheaf morphisms out of scalar extension are exactly maps to restricted coefficients. -/
def sheafExtensionHomEquiv (F : EtaleDerivedSections.ModuleSheaf X R)
    (E : EtaleDerivedSections.ModuleSheaf X S) :
    ((sheafExtendScalars φ X).obj F ⟶ E) ≃ (F ⟶ (sheafRestrictScalars φ X).obj E) :=
  (sheafExtendRestrictScalarsAdj φ X).homEquiv F E

/-- The forward universal correspondence precomposes the restricted map with the unit. -/
theorem sheafExtensionHomEquiv_apply (F : EtaleDerivedSections.ModuleSheaf X R)
    (E : EtaleDerivedSections.ModuleSheaf X S) (f : (sheafExtendScalars φ X).obj F ⟶ E) :
    sheafExtensionHomEquiv φ X F E f =
      (sheafExtensionUnit φ X).app F ≫ (sheafRestrictScalars φ X).map f :=
  (sheafExtendRestrictScalarsAdj φ X).homEquiv_unit F E f

/-- Extend a morphism to restricted coefficients uniquely through the tensor sheaf. -/
def sheafExtensionLift {F : EtaleDerivedSections.ModuleSheaf X R}
    {E : EtaleDerivedSections.ModuleSheaf X S} (f : F ⟶ (sheafRestrictScalars φ X).obj E) :
    (sheafExtendScalars φ X).obj F ⟶ E :=
  (sheafExtensionHomEquiv φ X F E).symm f

/-- The constructed lift factors the given coefficient morphism. -/
@[simp] theorem sheafExtensionUnit_lift {F : EtaleDerivedSections.ModuleSheaf X R}
    {E : EtaleDerivedSections.ModuleSheaf X S} (f : F ⟶ (sheafRestrictScalars φ X).obj E) :
    (sheafExtensionUnit φ X).app F ≫
      (sheafRestrictScalars φ X).map (sheafExtensionLift φ X f) = f := by
  rw [← sheafExtensionHomEquiv_apply]
  exact (sheafExtensionHomEquiv φ X F E).apply_symm_apply f

/-- A sheaf morphism satisfying the unit equation is the constructed lift. -/
theorem sheafExtensionLift_unique {F : EtaleDerivedSections.ModuleSheaf X R}
    {E : EtaleDerivedSections.ModuleSheaf X S} (f : F ⟶ (sheafRestrictScalars φ X).obj E)
    (g : (sheafExtendScalars φ X).obj F ⟶ E)
    (h : (sheafExtensionUnit φ X).app F ≫ (sheafRestrictScalars φ X).map g = f) :
    g = sheafExtensionLift φ X f := by
  apply (sheafExtensionHomEquiv φ X F E).injective
  rw [sheafExtensionHomEquiv_apply, h]
  exact ((sheafExtensionHomEquiv φ X F E).apply_symm_apply f).symm

/-- Universal extension is natural in the source coefficient sheaf. -/
theorem sheafExtensionLift_precomp {F F' : EtaleDerivedSections.ModuleSheaf X R}
    {E : EtaleDerivedSections.ModuleSheaf X S} (a : F' ⟶ F)
    (f : F ⟶ (sheafRestrictScalars φ X).obj E) :
    sheafExtensionLift φ X (a ≫ f) =
      (sheafExtendScalars φ X).map a ≫ sheafExtensionLift φ X f :=
  (sheafExtendRestrictScalarsAdj φ X).homEquiv_naturality_left_symm a f

/-- Universal extension is natural in the target coefficient sheaf. -/
theorem sheafExtensionLift_postcomp {F : EtaleDerivedSections.ModuleSheaf X R}
    {E E' : EtaleDerivedSections.ModuleSheaf X S}
    (f : F ⟶ (sheafRestrictScalars φ X).obj E) (b : E ⟶ E') :
    sheafExtensionLift φ X (f ≫ (sheafRestrictScalars φ X).map b) =
      sheafExtensionLift φ X f ≫ b :=
  (sheafExtendRestrictScalarsAdj φ X).homEquiv_naturality_right_symm f b

end Langlands.Geometry.EtaleCohomologyAction
