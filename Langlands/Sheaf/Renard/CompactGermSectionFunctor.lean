import Langlands.Sheaf.Renard.CompactGermSections
import Langlands.Sheaf.Renard.BasisSheaf
import Mathlib.CategoryTheory.Whiskering

/-!
# Fixed-open compact germ-section functors

Actual presheaf morphisms act through the original stalk maps. Forgetting
compactness is natural, including after the actual full-subcategory inclusions.
-/

noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- Unrestricted locally represented germ sections at a fixed actual open. -/
def rawGermSectionsFunctor (B : OpenBasis X) (U : Opens X) :
    RawPresheaf.{u,v} B ⥤ AddCommGrpCat.{max u v} where
  obj F := AddCommGrpCat.of (GermSections F U)
  map φ := AddCommGrpCat.ofHom (germSectionsMap φ U)
  map_id F := by
    apply AddCommGrpCat.ext
    intro s
    exact DFunLike.congr_fun (germSectionsMap_id F U) s
  map_comp φ ψ := by
    apply AddCommGrpCat.ext
    intro s
    exact DFunLike.congr_fun (germSectionsMap_comp φ ψ U) s

/-- Compactly supported sections of the same actual germ model at a fixed open. -/
def rawCompactGermSectionsFunctor (B : OpenBasis X) (U : Opens X) :
    RawPresheaf.{u,v} B ⥤ AddCommGrpCat.{max u v} where
  obj F := AddCommGrpCat.of (CompactGermSections F U)
  map φ := AddCommGrpCat.ofHom (compactGermSectionsMap φ U)
  map_id F := by
    apply AddCommGrpCat.ext
    intro s
    exact DFunLike.congr_fun (compactGermSectionsMap_id F U) s
  map_comp φ ψ := by
    apply AddCommGrpCat.ext
    intro s
    exact DFunLike.congr_fun (compactGermSectionsMap_comp φ ψ U) s

@[simp]
theorem rawGermSectionsFunctor_obj (F : RawPresheaf.{u,v} B) (U : Opens X) :
    (rawGermSectionsFunctor B U).obj F = AddCommGrpCat.of (GermSections F U) := rfl

@[simp]
theorem rawCompactGermSectionsFunctor_obj (F : RawPresheaf.{u,v} B) (U : Opens X) :
    (rawCompactGermSectionsFunctor B U).obj F =
      AddCommGrpCat.of (CompactGermSections F U) := rfl

@[simp]
theorem rawGermSectionsFunctor_map_hom {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) :
    ((rawGermSectionsFunctor B U).map φ).hom = germSectionsMap φ U := rfl

@[simp]
theorem rawCompactGermSectionsFunctor_map_hom {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) :
    ((rawCompactGermSectionsFunctor B U).map φ).hom = compactGermSectionsMap φ U := rfl

@[simp]
theorem rawGermSectionsFunctor_map_apply {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) (s : GermSections F U) (x : U) :
    ((rawGermSectionsFunctor B U).map φ s).val x =
      rawStalkMap φ x.val (s.val x) := rfl

@[simp]
theorem rawCompactGermSectionsFunctor_map_apply {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) (s : CompactGermSections F U) (x : U) :
    ((rawCompactGermSectionsFunctor B U).map φ s).val.val x =
      rawStalkMap φ x.val (s.val.val x) := rfl

/-- The injective additive inclusions form a natural transformation. -/
def rawCompactGermSectionsNatInclusion (B : OpenBasis X) (U : Opens X) :
    rawCompactGermSectionsFunctor.{u,v} B U ⟶ rawGermSectionsFunctor B U where
  app F := AddCommGrpCat.ofHom (compactGermSectionsInclusionHom F U)
  naturality _ _ _ := rfl

@[simp]
theorem rawCompactGermSectionsNatInclusion_app_hom
    (F : RawPresheaf.{u,v} B) (U : Opens X) :
    ((rawCompactGermSectionsNatInclusion B U).app F).hom =
      compactGermSectionsInclusionHom F U := rfl

@[simp]
theorem rawCompactGermSectionsNatInclusion_app
    (F : RawPresheaf.{u,v} B) (U : Opens X) (s : CompactGermSections F U) :
    (rawCompactGermSectionsNatInclusion B U).app F s =
      compactGermSectionsInclusion F U s := rfl

@[simp]
theorem rawCompactGermSectionsNatInclusion_app_value
    (F : RawPresheaf.{u,v} B) (U : Opens X) (s : CompactGermSections F U) (x : U) :
    ((rawCompactGermSectionsNatInclusion B U).app F s).val x = s.val.val x := rfl

theorem rawCompactGermSectionsNatInclusion_app_injective
    (F : RawPresheaf.{u,v} B) (U : Opens X) :
    Function.Injective ((rawCompactGermSectionsNatInclusion B U).app F) :=
  compactGermSectionsInclusionHom_injective F U

/-- Unrestricted sections restricted along the actual normalization inclusion. -/
def germSectionsFunctor (B : OpenBasis X) (U : Opens X) :
    Presheaf.{u,v} B ⥤ AddCommGrpCat.{max u v} :=
  presheafInclusion B ⋙ rawGermSectionsFunctor B U

/-- Compact sections restricted along the actual normalization inclusion. -/
def compactGermSectionsFunctor (B : OpenBasis X) (U : Opens X) :
    Presheaf.{u,v} B ⥤ AddCommGrpCat.{max u v} :=
  presheafInclusion B ⋙ rawCompactGermSectionsFunctor B U

/-- Forget compactness naturally on normalized presheaves. -/
def compactGermSectionsNatInclusion (B : OpenBasis X) (U : Opens X) :
    compactGermSectionsFunctor.{u,v} B U ⟶ germSectionsFunctor B U :=
  Functor.whiskerLeft (presheafInclusion B) (rawCompactGermSectionsNatInclusion B U)

@[simp]
theorem germSectionsFunctor_obj (F : Presheaf.{u,v} B) (U : Opens X) :
    (germSectionsFunctor B U).obj F = AddCommGrpCat.of (GermSections F.obj U) := rfl

@[simp]
theorem compactGermSectionsFunctor_obj (F : Presheaf.{u,v} B) (U : Opens X) :
    (compactGermSectionsFunctor B U).obj F =
      AddCommGrpCat.of (CompactGermSections F.obj U) := rfl

@[simp]
theorem germSectionsFunctor_map_hom {F G : Presheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) :
    ((germSectionsFunctor B U).map φ).hom = germSectionsMap φ.hom U := rfl

@[simp]
theorem compactGermSectionsFunctor_map_hom {F G : Presheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) :
    ((compactGermSectionsFunctor B U).map φ).hom =
      compactGermSectionsMap φ.hom U := rfl

@[simp]
theorem compactGermSectionsFunctor_map_apply {F G : Presheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) (s : CompactGermSections F.obj U) (x : U) :
    ((compactGermSectionsFunctor B U).map φ s).val.val x =
      rawStalkMap φ.hom x.val (s.val.val x) := rfl

@[simp]
theorem compactGermSectionsNatInclusion_app_hom (F : Presheaf.{u,v} B) (U : Opens X) :
    ((compactGermSectionsNatInclusion B U).app F).hom =
      compactGermSectionsInclusionHom F.obj U := rfl

@[simp]
theorem compactGermSectionsNatInclusion_app_value (F : Presheaf.{u,v} B) (U : Opens X)
    (s : CompactGermSections F.obj U) (x : U) :
    ((compactGermSectionsNatInclusion B U).app F s).val x = s.val.val x := rfl

/-- Unrestricted germ sections of a basis sheaf at any actual open. -/
def basisSheafGermSectionsFunctor (B : OpenBasis X) (U : Opens X) :
    BasisSheaf.{u,v} B ⥤ AddCommGrpCat.{max u v} :=
  sheafForget B ⋙ germSectionsFunctor B U

/-- Compact germ sections of a basis sheaf, using its unchanged underlying raw object. -/
def basisSheafCompactGermSectionsFunctor (B : OpenBasis X) (U : Opens X) :
    BasisSheaf.{u,v} B ⥤ AddCommGrpCat.{max u v} :=
  sheafForget B ⋙ compactGermSectionsFunctor B U

/-- The basis-sheaf version of the same natural inclusion. -/
def basisSheafCompactGermSectionsNatInclusion (B : OpenBasis X) (U : Opens X) :
    basisSheafCompactGermSectionsFunctor.{u,v} B U ⟶
      basisSheafGermSectionsFunctor B U :=
  Functor.whiskerLeft (sheafForget B) (compactGermSectionsNatInclusion B U)

@[simp]
theorem basisSheafGermSectionsFunctor_obj (F : BasisSheaf.{u,v} B) (U : Opens X) :
    (basisSheafGermSectionsFunctor B U).obj F =
      AddCommGrpCat.of (GermSections F.obj.obj U) := rfl

@[simp]
theorem basisSheafCompactGermSectionsFunctor_obj
    (F : BasisSheaf.{u,v} B) (U : Opens X) :
    (basisSheafCompactGermSectionsFunctor B U).obj F =
      AddCommGrpCat.of (CompactGermSections F.obj.obj U) := rfl

@[simp]
theorem basisSheafGermSectionsFunctor_map_hom {F G : BasisSheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) :
    ((basisSheafGermSectionsFunctor B U).map φ).hom =
      germSectionsMap φ.hom.hom U := rfl

@[simp]
theorem basisSheafCompactGermSectionsFunctor_map_hom
    {F G : BasisSheaf.{u,v} B} (φ : F ⟶ G) (U : Opens X) :
    ((basisSheafCompactGermSectionsFunctor B U).map φ).hom =
      compactGermSectionsMap φ.hom.hom U := rfl

@[simp]
theorem basisSheafCompactGermSectionsFunctor_map_apply
    {F G : BasisSheaf.{u,v} B} (φ : F ⟶ G) (U : Opens X)
    (s : CompactGermSections F.obj.obj U) (x : U) :
    ((basisSheafCompactGermSectionsFunctor B U).map φ s).val.val x =
      rawStalkMap φ.hom.hom x.val (s.val.val x) := rfl

@[simp]
theorem basisSheafCompactGermSectionsNatInclusion_app_hom
    (F : BasisSheaf.{u,v} B) (U : Opens X) :
    ((basisSheafCompactGermSectionsNatInclusion B U).app F).hom =
      compactGermSectionsInclusionHom F.obj.obj U := rfl

@[simp]
theorem basisSheafCompactGermSectionsNatInclusion_app_value
    (F : BasisSheaf.{u,v} B) (U : Opens X) (s : CompactGermSections F.obj.obj U) (x : U) :
    ((basisSheafCompactGermSectionsNatInclusion B U).app F s).val x = s.val.val x := rfl

end Langlands.Sheaf.Renard
