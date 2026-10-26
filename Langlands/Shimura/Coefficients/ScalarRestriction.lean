import Langlands.Shimura.Coefficients.Associated
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Scalar restriction of associated coefficient sheaves -/

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C : Type w} [Category.{v} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable {G : Type u} [Group G] (Y : Action C G)

local instance : HasLimitsOfShape (SingleObj G) (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfShape

local instance : HasLimitsOfShape (SingleObj G) (ModuleCat.{u} S) :=
  ModuleCat.hasLimitsOfShape

/-- Product sections and restriction of module scalars have the same section data. -/
def productSheafRestrictScalarsIso :
    productSheaf J Y.V ⋙ sheafCompose J (ModuleCat.restrictScalars.{u} φ) ≅
      sheafCompose J (ModuleCat.restrictScalars.{u} φ) ⋙ productSheaf J Y.V :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- Scalar restriction preserves the inverse-deck diagonal diagram. -/
def invariantDiagramRestrictScalarsIso :
    invariantDiagram J Y ⋙
        (Functor.whiskeringRight _ _ _).obj (sheafCompose J (ModuleCat.restrictScalars.{u} φ)) ≅
      (sheafCompose J (ModuleCat.restrictScalars.{u} φ)).mapAction G ⋙
        invariantDiagram J Y :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _))

local instance scalarRestrictionPreservesGroupLimits :
    PreservesLimitsOfShape (SingleObj G)
      (sheafCompose J (ModuleCat.restrictScalars.{u} φ)) := by
  let : PreservesLimitsOfShape (SingleObj G) (ModuleCat.restrictScalars.{u} φ) :=
    ⟨fun {F} => ModuleCat.preservesLimit_restrictScalars φ F⟩
  let : PreservesLimitsOfShape (SingleObj G)
      (sheafCompose J (ModuleCat.restrictScalars.{u} φ) ⋙ sheafToPresheaf J _) :=
    inferInstanceAs (PreservesLimitsOfShape (SingleObj G)
      (sheafToPresheaf J _ ⋙
        (Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{u} φ)))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J _)

/-- Restricting scalars commutes naturally with the actual invariant-limit sheaf. -/
def associatedRestrictScalarsIso :
    associatedFunctor J Y ⋙ sheafCompose J (ModuleCat.restrictScalars.{u} φ) ≅
      (sheafCompose J (ModuleCat.restrictScalars.{u} φ)).mapAction G ⋙
        associatedFunctor J Y :=
  Functor.isoWhiskerLeft (invariantDiagram J Y)
      (preservesLimitNatIso (sheafCompose J (ModuleCat.restrictScalars.{u} φ))) ≪≫
    Functor.isoWhiskerRight (invariantDiagramRestrictScalarsIso J φ Y) lim

@[reassoc (attr := simp)]
theorem associatedRestrictScalarsIso_hom_inclusion
    (F : Action (Sheaf J (ModuleCat.{u} S)) G) :
    (associatedRestrictScalarsIso J φ Y).hom.app F ≫
        inclusion J Y ((sheafCompose J (ModuleCat.restrictScalars.{u} φ)).mapAction G |>.obj F) =
      (sheafCompose J (ModuleCat.restrictScalars.{u} φ)).map (inclusion J Y F) := by
  change (preservesLimitIso _ _).hom ≫
      lim.map ((invariantDiagramRestrictScalarsIso J φ Y).hom.app F) ≫
      limit.π _ (SingleObj.star G) = _
  erw [limMap_π]
  simp [invariantDiagramRestrictScalarsIso, inclusion]

@[reassoc (attr := simp)]
theorem associatedRestrictScalarsIso_inv_inclusion
    (F : Action (Sheaf J (ModuleCat.{u} S)) G) :
    (associatedRestrictScalarsIso J φ Y).inv.app F ≫
        (sheafCompose J (ModuleCat.restrictScalars.{u} φ)).map (inclusion J Y F) =
      inclusion J Y ((sheafCompose J (ModuleCat.restrictScalars.{u} φ)).mapAction G |>.obj F) := by
  rw [← associatedRestrictScalarsIso_hom_inclusion J φ Y F, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp]

end Langlands.Shimura.Coefficients
