/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenImageDirectImageComparisonUnit
import all WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonRestriction

/-! # Compatibility of the ordinary open-image comparison with nested restriction

Source: Stacks Project, Cohomology, Tags 08FE and 08BV.
(blueprint: lem-pc-open-image-direct-image-comparison-restriction).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AlgebraicGeometry

/-- The fixed ordinary comparison commutes with restriction to any smaller open.
Source: Stacks Project, Tags 08FE and 08BV.
(blueprint: lem-pc-open-image-direct-image-comparison-restriction).
Proof: Open direct image is fully faithful, so the larger-open restriction
of its adjunction unit is invertible. Applying the overlap restriction and
conjugating by schemeOpenRestrictionCompIso shows that restriction of this
unit to the smaller open is invertible as well. Unit compatibility of the
ordinary comparison transfers this property to the direct image of the
inverse-image-open unit. The smaller-open adjunction Hom equivalence therefore
allows cancellation of that direct image in maps into the smaller-open image.
After precomposition by it, both sides become the smaller-open unit: use
schemeOpenModuleImage_unit_restriction on X and Y and the comparison unit
identity at U and W. This proves equality without expanding the nested mate
on sections. Empty and repeated opens need no exception; all the adjunction
identities and invertibilities continue to hold. -/
theorem schemeOpenImageDirectImageComparison_restriction
    (X Y : Scheme.{u}) (h : X ⟶ Y) {W U : Y.Opens} (i : W ⟶ U)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (schemeOpenImageDirectImageComparison h U).hom.app M ≫
        (schemeOpenModuleImageRestriction Y i).app
          ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).obj M) =
      (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).map
          ((schemeOpenModuleImageRestriction X ((Opens.map h.base).map i)).app M) ≫
        (schemeOpenImageDirectImageComparison h W).hom.app M := by
  let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
  let L := schemeOpenRestriction Y W
  let η := F.map ((schemeOpenModuleAdjunction X (h ⁻¹ᵁ U)).unit.app M)
  let c := (schemeOpenImageDirectImageComparison h U).hom.app M
  have hu : η ≫ c = (schemeOpenModuleAdjunction Y U).unit.app (F.obj M) :=
    schemeOpenImageDirectImageComparison_unit X Y h U M
  have : IsIso (L.map (η ≫ c)) := by
    rw [hu]
    exact isIso_smaller_restriction_unit Y i (F.obj M)
  have : IsIso (L.map η) := by
    have : IsIso (L.map η ≫ L.map c) := by rw [← L.map_comp]; infer_instance
    exact IsIso.of_isIso_comp_right (L.map η) (L.map c)
  have : Epi ((schemeOpenRestriction Y W).map η) :=
    (@CategoryTheory.IsIso.epi_of_iso _ _ _ _ (L.map η) ‹IsIso (L.map η)›)
  apply cancel_into_right_adjoint (schemeOpenModuleAdjunction Y W) η
  change η ≫ c ≫ _ = η ≫ F.map _ ≫ _
  rw [← Category.assoc, hu, schemeOpenModuleImage_unit_restriction]
  rw [← Category.assoc, ← F.map_comp,
    schemeOpenModuleImage_unit_restriction, schemeOpenImageDirectImageComparison_unit]

end AlgebraicGeometry
