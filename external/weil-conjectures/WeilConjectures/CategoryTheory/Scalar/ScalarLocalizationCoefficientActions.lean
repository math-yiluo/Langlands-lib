/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationRing
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Coefficient actions for scalar localization

Source: Bhatt–Scholze, Proposition 6.8.14(2).
(blueprint: def-weil-pbc-scalar-localization-coefficient-actions)

These are the canonical section actions, shared by the scalar-localization telescope
and its derived-Hom comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- Image of a compatible coefficient family is again compatible.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: def-weil-pbc-scalar-localization-coefficient-actions).
Proof: commute each restriction with the ring-sheaf morphism, and then use the
restriction compatibility of the original family. -/
theorem scalarLocalizationSectionsMap_mem {R S : Sheaf J CommRingCat.{u}}
    (f : R ⟶ S) (a : RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    (fun U ↦ f.hom.app U (a.val U)) ∈
      RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat) := by
  intro U V g
  change S.obj.map g (f.hom.app U (a.val U)) = f.hom.app V (a.val V)
  have h := ConcreteCategory.congr_hom (f.hom.naturality g) (a.val U)
  change f.hom.app V (R.obj.map g (a.val U)) =
    S.obj.map g (f.hom.app U (a.val U)) at h
  rw [← h]
  exact congrArg (f.hom.app V) (a.property g)

/-- The map of global coefficient rings induced by a ring-sheaf morphism.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: def-weil-pbc-scalar-localization-coefficient-actions). -/
def scalarLocalizationSectionsMap {R S : Sheaf J CommRingCat.{u}} (f : R ⟶ S) :
    RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat) →+*
      RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat) :=
  (RingHom.pi (fun U ↦ (f.hom.app U).hom.comp
    ((Pi.evalRingHom (fun V ↦ R.obj.obj V) U).comp
      (RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)).subtype))).codRestrict
    (RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    (scalarLocalizationSectionsMap_mem f)

/-- The usual coefficient action on module-sheaf Homs, by restriction from global sections.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: def-weil-pbc-scalar-localization-coefficient-actions). -/
@[instance_reducible]
def scalarLocalizationCoefficientLinear (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    Linear A (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  letI : Linear (RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.homLinear R.obj
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).property
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) a
    smul_comp := fun M N P r f g ↦ Linear.smul_comp M N P (a r) f g
    comp_smul := fun M N P f r g ↦ Linear.comp_smul M N P f (a r) g }

/-- The localized coefficient is a unit in the ring of sections of R[1/t].
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: def-weil-pbc-scalar-localization-coefficient-actions).
Proof: the sectionwise image of t is a unit by localization. Its inverses commute
with restriction by uniqueness of inverses. Apply sheafification to this section
and its inverse; their products remain one, also for the zero ring and empty site. -/
theorem scalarLocalizationSections_isUnit (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A) :
    IsUnit ((scalarLocalizationSectionsMap
      (ringedLocalizationRingUnit R (a t))).comp a t) := by
  classical
  let b := (scalarLocalizationSectionsMap (ringedLocalizationRingUnit R (a t))).comp a t
  have hu (U : Cᵒᵖ) : IsUnit (b.val U) := by
    change IsUnit ((toSheafify J (ringedLocalizationRingPresheaf R (a t))).app U
      (algebraMap (R.obj.obj U) (ringedSectionLocalizationCarrier R (a t) U)
        ((a t).val U)))
    exact (IsLocalization.Away.algebraMap_isUnit (R := R.obj.obj U)
      (S := ringedSectionLocalizationCarrier R (a t) U) ((a t).val U)).map
        ((toSheafify J (ringedLocalizationRingPresheaf R (a t))).app U).hom
  choose c hc using fun U ↦ (hu U).exists_right_inv
  let d : RingCat.sectionsSubring
      ((ringedLocalizationRing R (a t)).obj ⋙ forget₂ CommRingCat RingCat) :=
    ⟨c, by
      intro U V g
      let ρ := (((ringedLocalizationRing R (a t)).obj ⋙
        forget₂ CommRingCat RingCat).map g).hom
      change ρ (c U) = c V
      apply (hu V).mul_left_cancel
      have hb : ρ (b.val U) = b.val V := b.property g
      calc
        b.val V * ρ (c U) = ρ (b.val U * c U) := by rw [← hb, map_mul]
        _ = 1 := by rw [hc, map_one]
        _ = b.val V * c V := (hc V).symm⟩
  exact IsUnit.of_mul_eq_one d (by ext U; exact hc U)

/-- The canonical A[1/t]-algebra structure of the localized ring sheaf.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: def-weil-pbc-scalar-localization-coefficient-actions). -/
def scalarLocalizationCoefficientMap (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A) :
    Localization.Away t →+* RingCat.sectionsSubring
      ((ringedLocalizationRing R (a t)).obj ⋙ forget₂ CommRingCat RingCat) :=
  IsLocalization.Away.lift t
    (g := (scalarLocalizationSectionsMap (ringedLocalizationRingUnit R (a t))).comp a)
    (scalarLocalizationSections_isUnit A R a t)

end CategoryTheory
