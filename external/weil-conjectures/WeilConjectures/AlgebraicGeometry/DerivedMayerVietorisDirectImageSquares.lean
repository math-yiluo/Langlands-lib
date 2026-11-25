/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenComparisonUnit
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenComparisonRestriction

/-! # DerivedMayerVietorisDirectImageSquares

Source: Stacks Project, Cohomology, Tags 08BV and 0D5T; Derived Categories of Schemes,
Tag 0DJ9 (blueprint: lem-pc-derived-mayer-vietoris-direct-image-squares).
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

/-- The recorded comparisons commute with the first two arrows of the explicit triangles.
Source: Stacks Tags 0D5T and 0DJ9
(blueprint: lem-pc-derived-mayer-vietoris-direct-image-squares).

Proof:
1. Compute both sides on the fixed K-injective representative of E. Restriction to an
   inverse-image open is K-injective. Direct image and open restriction are identified
   sectionwise, and the composition comparison identifies their two pushforwards.
2. The sectionwise identity carries the unit on X to the unit on Y. Combining the
   two open squares with the localization biproduct comparison gives the first square.
3. For the second square, the same sectionwise identity commutes with the two nested
   restriction maps to the intersection. The mate formula for the derived restriction
   maps transports this identity to the derived category. Additivity preserves their
   difference, and the biproduct comparison assembles the second square.
4. Transport from the representative to E by the resolution isomorphism. Naturality
   of the functor comparisons and of units and restrictions gives the stated equations.
-/
theorem schemeMV_directImage_squares
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    (hcover : U ⊔ V = ⊤)
    (hcover' : (h ⁻¹ᵁ U) ⊔ (h ⁻¹ᵁ V) = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) :
    (schemeMVImageTriangle h
      (schemeMVTriangle X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) hcover' E)).mor₁ ≫
        (schemeMVMiddleComparison h U V E).hom =
      (schemeMVTriangle Y U V hcover ((schemeDerivedDirectImage h).obj E)).mor₁ ∧
    (schemeMVImageTriangle h
      (schemeMVTriangle X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) hcover' E)).mor₂ ≫
        (schemeMVOpenComparison h (U ⊓ V) E).hom =
      (schemeMVMiddleComparison h U V E).hom ≫
        (schemeMVTriangle Y U V hcover ((schemeDerivedDirectImage h).obj E)).mor₂ := by
  let F := schemeDerivedDirectImage h
  have : F.Additive := inferInstance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  constructor
  · change F.map (biprod.lift _ _) ≫
      ((F.mapBiprod _ _).hom ≫ (biprod.mapIso _ _).hom) = biprod.lift _ _
    rw [← Category.assoc, biprod.map_lift_mapBiprod]
    apply biprod.hom_ext
    · simpa only [biprod.mapIso_hom, Category.assoc, biprod.map_fst,
        biprod.lift_fst_assoc, biprod.lift_fst] using
        schemeMVOpenComparison_unit X Y h U E
    · simpa only [biprod.mapIso_hom, Category.assoc, biprod.map_snd,
        biprod.lift_snd_assoc, biprod.lift_snd] using
        schemeMVOpenComparison_unit X Y h V E
  · change F.map (biprod.desc _ _) ≫ (schemeMVOpenComparison h (U ⊓ V) E).hom =
      ((F.mapBiprod _ _).hom ≫ (biprod.mapIso _ _).hom) ≫ biprod.desc _ _
    rw [← biprod.mapBiprod_hom_desc]
    simp only [Category.assoc]
    apply congrArg (fun f ↦ (F.mapBiprod _ _).hom ≫ f)
    apply biprod.hom_ext'
    · simpa only [F, Functor.comp_obj, Scheme.Hom.preimage_inf,
        biprod.mapIso_hom, ← Category.assoc, biprod.inl_desc,
        biprod.inl_desc_assoc,
        biprod.inl_map_assoc, Category.assoc] using!
        schemeMVOpenComparison_restriction.{u, w} X Y h (U ⊓ V) U inf_le_left E
    · simpa only [F, Functor.comp_obj, Scheme.Hom.preimage_inf,
        biprod.mapIso_hom, ← Category.assoc, biprod.inr_desc,
        biprod.inr_desc_assoc,
        biprod.inr_map_assoc, Category.assoc, Functor.map_neg,
        Preadditive.neg_comp, Preadditive.comp_neg] using!
        congrArg Neg.neg
          (schemeMVOpenComparison_restriction.{u, w} X Y h (U ⊓ V) V inf_le_right E)

end AlgebraicGeometry
