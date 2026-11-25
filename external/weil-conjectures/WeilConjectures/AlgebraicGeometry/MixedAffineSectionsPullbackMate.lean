/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomPullbackComparison
public import WeilConjectures.AlgebraicGeometry.MixedGlobalExtension
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsKFlatComparisonIso
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackModuleModel

/-! # Affine sections transport the pullback adjunction mate

Source: Stacks Project, Tags 08DW(2), 06Z0, 08HY and 0D5T.
(blueprint: lem-sc-mixed-affine-sections-pullback-mate).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Affine scalar extension of sections agrees with sheaf pullback, including mates.
No perfectness, flatness, or invertibility of the input morphism is assumed.
Source: Stacks Project, perfect.tex, Tags 06Z0 and 08DW(2); cohomology.tex,
Tags 08HY and 0D5T; duality.tex, Tag 0AA8, identification of the map beta.
(blueprint: lem-sc-mixed-affine-sections-pullback-mate).

Proof: Identify S and T with spectra of their global rings via isoSpec. The affine
quasi-coherent derived equivalence identifies E with a module complex. Resolve it
by a K-flat complex. Termwise tilde and the derived pullback counit identify its
pullback with derived extension of scalars. Derive the underived sections adjunction
using K-injective resolutions. The same tilde/scalar-extension identification
intertwines the adjunction units: both are induced on K-flat representatives by
x mapping to 1 tensor x. Uniqueness of the left adjoint to derived scalar restriction
therefore gives a unique unit-compatible comparison a for mixedGlobalExtension.
For theta, transpose a.hom followed by RGlobalSections(theta) under the fixed scalar
adjunction. Unit compatibility and naturality identify this transpose with derived
sections of the sheaf pullback adjunct of theta, followed by Leray. The right-derived
unit equation for mixedGlobalSectionsDirectImageIso fixes this last identification.
Injectivity of the scalar adjunction equivalence gives the displayed equation for
all L and theta at once. Work separately in the sheaf and module localizations;
localization uniqueness preserves the equations for independent morphism universes.
On an empty affine scheme or for E=0, these constructions give the unique zero map. -/
theorem exists_mixedAffineSectionsPullbackMate
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (g : T ⟶ S) (E : schemeDerivedCategory S)
    (hE : schemeDerivedQCohProperty S E) :
    ∃ a : (mixedGlobalExtension g).obj ((schemeDerivedGlobalSections S).obj E) ≅
        (schemeDerivedGlobalSections T).obj ((derivedPullback g).obj E),
      ∀ (L : schemeDerivedCategory T) (theta : (derivedPullback g).obj E ⟶ L),
        ((mixedGlobalExtensionAdjunction g).homEquiv _ _).symm
            ((schemeDerivedGlobalSections S).map
                ((schemeHomPullbackAdjunction g).homEquiv E L theta) ≫
              (mixedGlobalSectionsDirectImageIso g).hom.app L) =
          a.hom ≫ (schemeDerivedGlobalSections T).map theta := by
  let c (Q : schemeDerivedCategory S) :
      (mixedGlobalExtension g).obj ((schemeDerivedGlobalSections S).obj Q) ⟶
        (schemeDerivedGlobalSections T).obj ((derivedPullback g).obj Q) :=
    ((mixedGlobalExtensionAdjunction g).homEquiv _ _).symm
      ((schemeDerivedGlobalSections S).map ((schemeHomPullbackAdjunction g).unit.app Q) ≫
        (mixedGlobalSectionsDirectImageIso g).hom.app ((derivedPullback g).obj Q))
  have hc (Q Q' : schemeDerivedCategory S) (f : Q ⟶ Q') :
      (mixedGlobalExtension g).map ((schemeDerivedGlobalSections S).map f) ≫ c Q' =
        c Q ≫ (schemeDerivedGlobalSections T).map ((derivedPullback g).map f) := by
    apply ((mixedGlobalExtensionAdjunction g).homEquiv _ _).injective
    dsimp only [c]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hu := (schemeHomPullbackAdjunction g).unit.naturality f
    dsimp only [Functor.id_map, Functor.comp_map] at hu
    have hr := (mixedGlobalSectionsDirectImageIso g).hom.naturality
      ((derivedPullback g).map f)
    dsimp only [Functor.comp_map] at hr
    rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp,
      Category.assoc, hr, Category.assoc]
  obtain ⟨P, hP, ⟨e⟩, _⟩ := exists_affine_derivedPullback_module_model g E hE
  have hmodel : IsIso (c _) := mixedAffineSections_kFlat_comparison_isIso g P hP
  have hnat := hc _ _ e.hom
  have he : IsIso ((mixedGlobalExtension g).map
      ((schemeDerivedGlobalSections S).map e.hom)) := by infer_instance
  have hleft := IsIso.comp_isIso' he hmodel
  have : IsIso (c E ≫ (schemeDerivedGlobalSections T).map
      ((derivedPullback g).map e.hom)) := by rw [← hnat]; exact hleft
  have : IsIso (c E) := IsIso.of_isIso_comp_right _
    ((schemeDerivedGlobalSections T).map ((derivedPullback g).map e.hom))
  refine ⟨asIso (c E), ?_⟩
  intro L theta
  change _ = c E ≫ (schemeDerivedGlobalSections T).map theta
  apply ((mixedGlobalExtensionAdjunction g).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right]
  dsimp only [c]
  erw [Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  have h := (mixedGlobalSectionsDirectImageIso g).hom.naturality theta
  dsimp only [Functor.comp_map] at h
  rw [Category.assoc, h, Category.assoc]

end AlgebraicGeometry
