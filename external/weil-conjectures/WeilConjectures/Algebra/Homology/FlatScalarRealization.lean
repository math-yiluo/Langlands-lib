/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # The canonical scalar-realization functor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type (max u v)} [CommRing A] {R : Sheaf J CommRingCat.{max u v}}
  [HasSheafify J AddCommGrpCat.{max u v}]
  (α : realizationRing J A ⟶ R)

/-- The recorded sheafified scalar extension, on both objects and maps.
Source: Stacks Project, Modules on Sites, Tag 03EK
(auxiliary; not a blueprint node). -/
def flatScalarExtension (α : realizationRing J A ⟶ R) :
    realizationModules J A ⥤ SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) where
  obj M := changeOfRingsOfUniverses.{v, u, max u v, max u v} α M
  map f := changeOfRingsHomOfUniverses.{v, u, max u v, max u v} α _ f
  map_id M := by
    let L := PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
    let t : changeOfRingsPresheafOfUniverses.{v, u, max u v, max u v} α M ⟶
        changeOfRingsPresheafOfUniverses.{v, u, max u v, max u v} α M :=
      { app U := (ModuleCat.extendScalars (α.hom.app U).hom).map (𝟙 (M.val.obj U))
        naturality := changeOfRingsHom_naturalityOfUniverses.{v, u, max u v, max u v} α M (𝟙 M) }
    have ht : t = 𝟙 _ := by
      apply PresheafOfModules.hom_ext
      intro U
      exact (ModuleCat.extendScalars (α.hom.app U).hom).map_id _
    change L.map t = 𝟙 _
    rw [ht, L.map_id]
  map_comp {M N P} f g := by
    let L := PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
    let t {X Y : realizationModules J A} (h : X ⟶ Y) :
        changeOfRingsPresheafOfUniverses.{v, u, max u v, max u v} α X ⟶
          changeOfRingsPresheafOfUniverses.{v, u, max u v, max u v} α Y :=
      { app U := (ModuleCat.extendScalars (α.hom.app U).hom).map (h.val.app U)
        naturality := changeOfRingsHom_naturalityOfUniverses α X h }
    have ht : t (f ≫ g) = t f ≫ t g := by
      apply PresheafOfModules.hom_ext
      intro U
      exact (ModuleCat.extendScalars (α.hom.app U).hom).map_comp _ _
    change L.map (t (f ≫ g)) = L.map (t f) ≫ L.map (t g)
    rw [ht, L.map_comp]

/-- Additivity is inherited from sectionwise tensor and additive sheafification.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
instance flatScalarExtension_additive : (flatScalarExtension J α).Additive where
  map_add {M N} f g := by
    let L := PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
    let t (h : M ⟶ N) :
        changeOfRingsPresheafOfUniverses.{v, u, max u v, max u v} α M ⟶
          changeOfRingsPresheafOfUniverses.{v, u, max u v, max u v} α N :=
      { app U := (ModuleCat.extendScalars (α.hom.app U).hom).map (h.val.app U)
        naturality := changeOfRingsHom_naturalityOfUniverses α M h }
    have ht : t (f + g) = t f + t g := by
      apply PresheafOfModules.hom_ext
      intro U
      have : (ModuleCat.extendScalars (α.hom.app U).hom).Additive :=
        (ModuleCat.extendRestrictScalarsAdj (α.hom.app U).hom).left_adjoint_additive
      exact (ModuleCat.extendScalars (α.hom.app U).hom).map_add
        (f := f.val.app U) (g := g.val.app U)
    have : PreservesFiniteLimits L := by
      let := siteTensor_identity_locallyInjective
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      let := siteTensor_identity_locallySurjective
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      dsimp [L]
      infer_instance
    have : L.Additive := leftExactFunctor_le_additiveFunctor _ _ L this
    change L.map (t (f + g)) = L.map (t f) + L.map (t g)
    rw [ht, L.map_add]

/-- Constant module realization followed by the specified sheafified change of rings.
Source: Stacks 093J and 03EK (auxiliary; not a blueprint node). -/
def flatScalarRealization (α : realizationRing J A ⟶ R) :
    ModuleCat.{max u v} A ⥤ SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  commutativeSiteConstantModuleFunctor J A ⋙ flatScalarExtension J α

/-- Both factors of scalar realization are additive.
Source: Stacks 093J and 03EK (auxiliary; not a blueprint node). -/
instance flatScalarRealization_additive : (flatScalarRealization J α).Additive :=
  inferInstanceAs ((commutativeSiteConstantModuleFunctor J A ⋙
    flatScalarExtension J α).Additive)

end SheafOfModules
