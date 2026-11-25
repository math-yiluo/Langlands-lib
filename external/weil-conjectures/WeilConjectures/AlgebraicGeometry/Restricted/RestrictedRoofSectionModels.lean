/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareLocalClassModels
import WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward
import all WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import all WeilConjectures.AlgebraicGeometry.RestrictionResolutionLiftSections

/-! # Restriction and direct-image section models for injective roofs

## References

* Stacks Project, Cohomology, Tags 01E4 and 01FB
* Stacks Project, Cohomology, Tag 01E4
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

/-- Sections on an open are global sections after restricting the sheaf. -/
def restrictionSectionsIso {X : Scheme.{u}} (U : X.Opens) :
    restrictFunctor U.ι ⋙ RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u} ≅ RingedSpace.openModuleSections X.toRingedSpace U :=
  NatIso.ofComponents (fun M ↦ M.restrictAppIso U.ι ⊤ ≪≫
    M.presheaf.mapIso (eqToIso (congrArg op U.ι_image_top))) (by
      intro M N φ
      dsimp [RingedSpace.globalSectionsFunctor, RingedSpace.openModuleSections]
      simp only [restrictAppIso]
      exact (φ.mapPresheaf.naturality
        ((eqToIso (congrArg op U.ι_image_top)).hom)).symm)

private theorem coefficient_restriction_pullback {X Z : Scheme.{u}}
    (v : Z ⟶ X) (U : X.Opens) :
    IsPullback (v ⁻¹ᵁ U).ι (v.resLE U (v ⁻¹ᵁ U) le_rfl) v U.ι := by
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
    (isPullback_morphismRestrict v U).flip

private theorem restrictedDirectImageMap_eq {X Z : Scheme.{u}} (v : Z ⟶ X)
    {F : X.Modules} {G : Z.Modules} (φ : F ⟶ (pushforward v).obj G) (U : X.Opens) :
    restrictedDirectImageMap v φ U =
      (restrictFunctor U.ι).map φ ≫
        (pushforwardRestrictIso (coefficient_restriction_pullback v U)).hom.app G := by
  unfold restrictedDirectImageMap
  rw [Adjunction.homEquiv_naturality_left_symm]
  rfl

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Scheme.Modules.Hom
-- Normalize the fixed restriction comparison and its sheaf-module category instances.
private theorem restriction_pushforward_sections {X Z : Scheme.{u}} (v : Z ⟶ X)
    {G : Z.Modules} (J : InjectiveResolution G) (U : X.Opens)
    (R' : RestrictedResolutionSections J (v ⁻¹ᵁ U)) :
    letI := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
    letI : (restrictFunctor U.ι).Additive :=
      (restrictAdjunction U.ι).left_adjoint_additive
    letI : (RingedSpace.openModuleSections X.toRingedSpace U).Additive :=
      RingedSpace.openModuleSections_additive X.toRingedSpace U
    letI : (show X.Modules ⥤ AddCommGrpCat.{u} from
        RingedSpace.openModuleSections X.toRingedSpace U).PreservesZeroMorphisms := by
      dsimp only [Scheme.Modules, Scheme.Modules.Hom, Scheme.Modules.instCategory,
        Scheme.Modules.instAbelian]
      exact Functor.preservesZeroMorphisms_of_additive
        (RingedSpace.openModuleSections X.toRingedSpace U)
    letI : (restrictFunctor U.ι ⋙
        RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat.{u}).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_iso (restrictionSectionsIso U).symm
    let Γ := (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
    let P := (pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).mapHomologicalComplex
      (ComplexShape.up ℕ)
    let c := (NatIso.mapHomologicalComplex
      (pushforwardRestrictIso (coefficient_restriction_pullback v U))
        (ComplexShape.up ℕ)).app J.cocomplex ≪≫ P.mapIso R'.comparison.symm
    let a := pushforward_sections_iso (v.resLE U (v ⁻¹ᵁ U) le_rfl) R'.resolution.cocomplex
    Γ.map c.hom ≫ a.inv ≫ R'.sections.hom =
      ((NatIso.mapHomologicalComplex (restrictionSectionsIso U)
        (ComplexShape.up ℕ)).app
          (((pushforward v).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            J.cocomplex)).hom := by
  intro Γ P c a
  dsimp only [Scheme.Modules, Scheme.Modules.Hom, Scheme.Modules.instCategory,
    Scheme.Modules.instAbelian] at *
  apply HomologicalComplex.hom_ext
  intro n
  change Hom.app (c.hom.f n) ⊤ ≫ a.inv.f n ≫ R'.sections.hom.f n = _
  rw [R'.components n]
  have h := raw_lift_sections v (𝟙 ((pushforward v).obj (J.cocomplex.X n))) U
    (𝟙 _) ((HomologicalComplex.eval _ _ n).mapIso R'.comparison)
  dsimp only at h
  simp only [Category.id_comp, Hom.id_app, Category.comp_id] at h
  simp only [← Category.assoc] at h
  rw [Adjunction.homEquiv_naturality_right_symm] at h
  simp only [Category.assoc] at h
  have ht : (pushforwardRestrictIso (coefficient_restriction_pullback v U)).hom.app
      (J.cocomplex.X n) = restrictedDirectImageMap v (𝟙 _) U := by
    rw [restrictedDirectImageMap_eq, CategoryTheory.Functor.map_id, Category.id_comp]
  change Hom.app
      ((pushforwardRestrictIso (coefficient_restriction_pullback v U)).hom.app
        (J.cocomplex.X n) ≫
          (pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).map (R'.comparison.inv.f n)) ⊤ ≫
      (R'.resolution.cocomplex.X n).presheaf.map
        (eqToHom (by simp) : (⊤ : (v ⁻¹ᵁ U).toScheme.Opens) ⟶
          (v.resLE U (v ⁻¹ᵁ U) le_rfl) ⁻¹ᵁ (⊤ : U.toScheme.Opens)).op ≫
      Hom.app (R'.comparison.hom.f n) ⊤ ≫
      (restrictAppIso (v ⁻¹ᵁ U).ι (J.cocomplex.X n) ⊤).hom ≫
      (J.cocomplex.X n).presheaf.map (eqToHom (v ⁻¹ᵁ U).ι_image_top.symm).op =
    (restrictAppIso U.ι ((pushforward v).obj (J.cocomplex.X n)) ⊤).hom ≫
      ((pushforward v).obj (J.cocomplex.X n)).presheaf.map
        (eqToHom U.ι_image_top.symm).op
  rw [ht]
  exact h

end AlgebraicGeometry
