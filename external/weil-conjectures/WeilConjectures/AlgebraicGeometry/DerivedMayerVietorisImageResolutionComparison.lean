/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSplitTriangle
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparisonIntersection

/-! # Comparing the concrete Mayer--Vietoris sequences after direct image

Source: Stacks Project, Tags 08BV, 08FE and 0D5T.
(blueprint: lem-pc-mayer-vietoris-image-resolution-comparison).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

/-- A map of concrete short complexes realizes the normalized first and intersection maps.
Source: Stacks Project, Tag 08BV, concrete sequence; Tag 08FE, sectionwise comparison;
Tag 0D5T, derived composition comparison.
(blueprint: lem-pc-mayer-vietoris-image-resolution-comparison).

Proof: Put I = schemeMVResolution X E and J = schemeMVResolution Y (Rh_*E).
The computation isomorphism phi_I followed by the inverse resolution isomorphism
of J gives a derived map Q(h_*I) to Q(J). Because J is K-injective, represent
this map by an actual chain map f : h_*I to J, using fullness of localization
on morphisms into a K-injective complex. Apply open restriction and open direct
image to f for U, V and their intersection. The sectionwise identity of Tag
08FE identifies h_*(j_*I|h^-1(W)) with j_*(h_*I)|W, naturally in W.
The pair of these maps defines the middle component using the additive
biproduct comparison. Naturality of restriction units and of the difference
of restrictions gives both commuting squares, hence a map m of short complexes.
The first displayed identity is the defining localized equation for f.
For the third component, the right-derived unit equations characterizing
schemeMVDirectImageComposition and schemeMVOpenRestrictionComparison compute
these comparisons on I as the localized sectionwise identity. Insert the
comparison for I on the inverse-image intersection and for J on U intersect V,
and use naturality at f. The two resolution isomorphisms then give exactly the
second identity. This assertion contains no connecting morphism; it holds
without any cover assumption. Empty and repeated opens give the same sectionwise
identities, and no injectivity or K-injectivity of h_*I is required. -/
theorem schemeMV_image_resolution_comparison
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X)
    [(schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))
      (schemeMVResolution X E)).IsKInjective] :
    let I := schemeMVResolution X E
    let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
    let S := schemeMayerVietorisComplex X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) I
    let T := schemeMayerVietorisComplex Y U V J
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ∃ m : S.map F ⟶ T,
      (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom I).hom ≫
          DerivedCategory.Q.map m.τ₁ ≫
          (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).hom =
        (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom ∧
      (schemeDerivedDirectImage h).map
          (((schemeMVDerivedRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))) ⋙
              schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)).ι).map
              (schemeMVResolutionIso X E).inv ≫
            (schemeOpenModuleImageComplexComparison X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I
              (schemeMVAdjunction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)))).inv) ≫
          (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
            (schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I)).hom ≫
          DerivedCategory.Q.map m.τ₃ =
        (schemeMVOpenComparison h (U ⊓ V) E).hom ≫
          (((schemeMVDerivedRestriction Y (U ⊓ V)) ⋙
              schemeDerivedDirectImage (U ⊓ V).ι).map
              (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).inv ≫
            (schemeOpenModuleImageComplexComparison Y (U ⊓ V) J
              (schemeMVAdjunction Y (U ⊓ V))).inv) := by
  dsimp
  obtain ⟨f, hf⟩ := schemeMV_normalized_chain_map_exists X Y h E
  refine ⟨schemeMVImageChainMap (h := h) U V _ _ f, hf, ?_⟩
  exact schemeMV_image_resolution_comparison_intersection X Y h U V E f hf

end AlgebraicGeometry
