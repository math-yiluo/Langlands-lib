/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenComparisonUnit

/-! # Compatibility of the canonical single-open direct-image comparison

Source: Stacks Project, Tags 08FE, 0D5T and 08BV.
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

private theorem unit_comp_restriction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (W U : X.Opens) (hWU : W ≤ U) (E : schemeDerivedCategory X) :
    (schemeMVAdjunction X U).unit.app E ≫
        schemeDerivedOpenDirectImageRestriction X (homOfLE hWU)
          (schemeMVAdjunction X U) (schemeMVAdjunction X W) E =
      (schemeMVAdjunction X W).unit.app E := by
  let a := schemeMVAdjunction X U
  let b := schemeMVAdjunction X W
  let T := (schemeOpenOverlapRestriction X (homOfLE hWU)).mapDerivedCategory
  let α := schemeDerivedOpenRestrictionCompIso X (homOfLE hWU)
  change a.unit.app E ≫ (b.homEquiv _ _)
    (α.inv.app _ ≫ T.map (a.counit.app _) ≫ α.hom.app E) = b.unit.app E
  rw [← b.homEquiv_naturality_left]
  have ht : (schemeMVDerivedRestriction X W).map (a.unit.app E) ≫
      (α.inv.app _ ≫ T.map (a.counit.app _) ≫ α.hom.app E) = 𝟙 _ := by
    rw [← Category.assoc, ← Category.assoc, α.inv.naturality]
    simp only [Functor.comp_map, Category.assoc]
    erw [← T.map_comp_assoc, a.left_triangle_components, T.map_id, Category.id_comp]
    exact α.inv_hom_id_app E
  rw [ht]
  exact b.homEquiv_id E

private theorem isIso_smaller_unit (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (W U : X.Opens) (hWU : W ≤ U) (E : schemeDerivedCategory X) :
    IsIso ((schemeMVDerivedRestriction X W).map ((schemeMVAdjunction X U).unit.app E)) := by
  let R := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  have : R.Additive := RingedSpace.moduleDirectImage_additive _
  let a : schemeOpenRestriction X U ⊣ R := schemeOpenModuleAdjunction X U
  have : R.PreservesKInjectiveComplexes := a.preservesKInjectiveComplexes
  have : R.Full :=
    (Scheme.Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.full
  have : R.Faithful :=
    (Scheme.Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.faithful
  have : (schemeDerivedDirectImage U.ι).Full := inferInstance
  have : (schemeDerivedDirectImage U.ι).Faithful := inferInstance
  have : IsIso ((schemeMVDerivedRestriction X U).map
      ((schemeMVAdjunction X U).unit.app E)) := by infer_instance
  let T := (schemeOpenOverlapRestriction X (homOfLE hWU)).mapDerivedCategory
  have : IsIso (((schemeMVDerivedRestriction X U) ⋙ T).map
      ((schemeMVAdjunction X U).unit.app E)) := by
    change IsIso (T.map ((schemeMVDerivedRestriction X U).map
      ((schemeMVAdjunction X U).unit.app E)))
    infer_instance
  exact (NatIso.isIso_map_iff (schemeDerivedOpenRestrictionCompIso X (homOfLE hWU))
    ((schemeMVAdjunction X U).unit.app E)).mp inferInstance

private theorem cancel_into_right_adjoint
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {A B : C} {N : D} (u : A ⟶ B) [Epi (L.map u)]
    {f g : B ⟶ R.obj N} (h : u ≫ f = u ≫ g) : f = g := by
  apply (a.homEquiv _ _).symm.injective
  apply (cancel_epi (L.map u)).mp
  simpa only [← a.homEquiv_naturality_left_symm] using
    congrArg (fun v ↦ (a.homEquiv A N).symm v) h

/-- The canonical single-open comparison commutes with restriction for any
inclusion W ≤ U, before taking a biproduct or a signed difference.
Source: Stacks Project, Tags 08FE and 0D5T, their K-injective and composition
comparisons; Tag 08BV, the restriction arrow in the displayed sequence of complexes.

Proof: Each nested restriction mate composes with the U-unit to the W-unit.
This follows by naturality of the exact nested-restriction comparison and the
left triangle identity of the U-adjunction. Open direct image is fully faithful
and preserves K-injectives, since it is right adjoint to exact open restriction.
Consequently its right derived functor is fully faithful. The U-restriction of
the derived U-unit is therefore invertible. Restrict further to W and conjugate
by schemeDerivedOpenRestrictionCompIso to see that W-restriction of the U-unit
is invertible as well. By schemeMVOpenComparison_unit, the direct image of the
X-unit, followed by the comparison at U, is the Y-unit. Applying W-restriction
and cancelling that invertible comparison shows that W-restriction of the direct
image of the X-unit is invertible. The W-adjunction Hom equivalence now permits
cancellation of this direct image of the X-unit in maps into the W-direct-image
object. After precomposition by it, the left side is the direct image of the
X-unit at W, followed by its comparison, hence the Y-unit at W. The right side
is the Y-unit at U followed by the Y-restriction mate, hence the same Y-unit at W.
This proves the equality. It does not require a cover, a biproduct or a sign.
For W=U the same argument reduces to the triangle identity; for W empty the
right-adjoint target vanishes, and cancellation remains valid.
(blueprint: lem-pc-derived-mayer-vietoris-open-comparison-restriction). -/
theorem schemeMVOpenComparison_restriction
    (X Y : Scheme.{u}) (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (W U : Y.Opens) (hWU : W ≤ U) (E : schemeDerivedCategory X) :
    (schemeDerivedDirectImage h).map
        (schemeDerivedOpenDirectImageRestriction X (homOfLE (h.preimage_mono hWU))
          (schemeMVAdjunction X (h ⁻¹ᵁ U)) (schemeMVAdjunction X (h ⁻¹ᵁ W)) E) ≫
        (schemeMVOpenComparison h W E).hom =
      (schemeMVOpenComparison h U E).hom ≫
        schemeDerivedOpenDirectImageRestriction Y (homOfLE hWU)
          (schemeMVAdjunction Y U) (schemeMVAdjunction Y W)
          ((schemeDerivedDirectImage h).obj E) := by
  let F := schemeDerivedDirectImage h
  let L := schemeMVDerivedRestriction Y W
  let η := F.map ((schemeMVAdjunction X (h ⁻¹ᵁ U)).unit.app E)
  let c := (schemeMVOpenComparison h U E).hom
  have hu : η ≫ c = (schemeMVAdjunction Y U).unit.app (F.obj E) :=
    schemeMVOpenComparison_unit X Y h U E
  have : IsIso (L.map (η ≫ c)) := by
    rw [hu]
    exact isIso_smaller_unit Y W U hWU (F.obj E)
  have : IsIso (L.map η) := by
    have : IsIso (L.map η ≫ L.map c) := by rw [← L.map_comp]; infer_instance
    exact IsIso.of_isIso_comp_right (L.map η) (L.map c)
  apply cancel_into_right_adjoint (schemeMVAdjunction Y W) η
  change (η ≫ F.map _ ≫ (schemeMVOpenComparison h W E).hom) =
    η ≫ c ≫ _
  rw [← Category.assoc, ← F.map_comp]
  rw [unit_comp_restriction X (h ⁻¹ᵁ W) (h ⁻¹ᵁ U) (h.preimage_mono hWU) E]
  rw [schemeMVOpenComparison_unit]
  rw [← Category.assoc, hu, unit_comp_restriction Y W U hWU (F.obj E)]

end AlgebraicGeometry
