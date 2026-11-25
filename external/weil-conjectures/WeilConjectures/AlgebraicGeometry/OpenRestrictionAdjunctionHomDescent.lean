/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionLocalization
import WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction

/-! # Coherent descent through open restriction

Source: Stacks Project, Tags 08EU and 08FE.
(blueprint: lem-pc-open-restriction-adjunction-hom-descent).
-/

@[expose] public section

universe u w
open CategoryTheory
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
variable [HasDerivedCategory.{u}
  (SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ U).toScheme.toRingedSpace))]
variable [HasDerivedCategory.{u}
  (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]


private theorem localization_hom
    {C D CO DO : Type*} [Category* C] [Category* D] [Category* CO] [Category* DO]
    {F : C ⥤ D} {G : D ⥤ C} (p : F ⊣ G)
    (rY : C ⥤ CO) (WY : MorphismProperty C) [rY.IsLocalization WY]
    (rX : D ⥤ DO) (WX : MorphismProperty D) [rX.IsLocalization WX]
    (FO : CO ⥤ DO) (GO : DO ⥤ CO)
    [CatCommSq F rY rX FO] [CatCommSq G rX rY GO]
    (A : C) (B : D) (v : F.obj A ⟶ B) :
    rY.map (p.homEquiv A B v) ≫ (CatCommSq.iso G rX rY GO).hom.app B =
      (p.localization rY WY rX WX FO GO).homEquiv (rY.obj A) (rX.obj B)
        ((CatCommSq.iso F rY rX FO).inv.app A ≫ rX.map v) := by
  rw [p.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    p.localization_unit_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← GO.map_comp_assoc, Iso.hom_inv_id_app]
  erw [GO.map_id]
  rw [Category.id_comp]
  exact congrArg (fun k ↦ rY.map (p.unit.app A) ≫ k)
    ((CatCommSq.iso G rX rY GO).hom.naturality v)


/-- The adjunction descends coherently to the inverse-image open.
Source: Stacks Project, Tags 08EU (locality) and 08FE (direct-image restriction).
Proof: both exact derived restriction functors are localizations at the maps they make
invertible. Choose the pullback and direct-image restriction isomorphisms, allowing
independent localization universes. At the full inverse-image open, resLE agrees with
the canonical restricted morphism. The two isomorphisms give CatCommSq instances.
Mathlib's Adjunction.localization descends the supplied p to an adjunction q between
the chosen local pullback and direct image. Expand both Hom equivalences as unit
followed by direct image of the argument. The localization_unit_app formula expresses
q's unit on a restricted object. Cancel alpha with its inverse under the local direct
image functor; naturality of beta then gives the displayed identity for every v.
This argument is independent of tensor products, quasi-coherence, and projection mates.
Empty opens are covered by the same localization construction.
(blueprint: lem-pc-open-restriction-adjunction-hom-descent). -/
theorem exists_openRestriction_adjunction_hom_descent
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f) :
    let rX := (schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory
    let rY := (schemeOpenRestriction Y U).mapDerivedCategory
    ∃ (q : derivedPullback (f ∣_ U) ⊣ schemeDerivedDirectImage (f ∣_ U))
      (alpha : derivedPullback f ⋙ rX ≅ rY ⋙ derivedPullback (f ∣_ U))
      (beta : schemeDerivedDirectImage f ⋙ rY ≅ rX ⋙ schemeDerivedDirectImage (f ∣_ U)),
      ∀ (A : schemeDerivedCategory Y) (B : schemeDerivedCategory X)
        (v : (derivedPullback f).obj A ⟶ B),
        rY.map (p.homEquiv A B v) ≫ beta.hom.app B =
          q.homEquiv (rY.obj A) (rX.obj B) (alpha.inv.app A ≫ rX.map v)  := by
  intro rX rY
  let WX := (MorphismProperty.isomorphisms
    (schemeDerivedCategory (f ⁻¹ᵁ U).toScheme)).inverseImage rX
  let WY := (MorphismProperty.isomorphisms
    (schemeDerivedCategory U.toScheme)).inverseImage rY
  have : rX.IsLocalization WX := schemeDerivedOpenRestriction_isLocalization X (f ⁻¹ᵁ U)
  have : rY.IsLocalization WY := schemeDerivedOpenRestriction_isLocalization Y U
  have hAlpha := derivedPullback_openRestriction_iso_universes.{u, w, u}
    f (f ⁻¹ᵁ U) U le_rfl
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at hAlpha
  let alpha := Classical.choice hAlpha
  let beta := Classical.choice (schemeDerivedDirectImage_openRestriction.{u, w, w, u, u} f U)
  let : CatCommSq (derivedPullback f) rY rX (derivedPullback (f ∣_ U)) := ⟨alpha⟩
  let : CatCommSq (schemeDerivedDirectImage f) rX rY
      (schemeDerivedDirectImage (f ∣_ U)) := ⟨beta⟩
  let q := p.localization rY WY rX WX (derivedPullback (f ∣_ U))
    (schemeDerivedDirectImage (f ∣_ U))
  refine ⟨q, alpha, beta, ?_⟩
  intro A B v
  exact localization_hom p rY WY rX WX (derivedPullback (f ∣_ U))
    (schemeDerivedDirectImage (f ∣_ U)) A B v

end AlgebraicGeometry
