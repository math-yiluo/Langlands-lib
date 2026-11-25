/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.DerivedOpenIntersectionEssentialImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # Detecting isomorphisms of open direct images on an intersection

Source: Stacks Project, Tags 08FE and 08DG.
(blueprint: lem-sc-derived-open-intersection-iso-detection).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem reflects_on_essential_image
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) [R.Full] [R.Faithful] {A B : C} (f : A ⟶ B)
    (hA : R.essImage A) (hB : R.essImage B) (hf : IsIso (L.map f)) : IsIso f := by
  have := hf
  have := (a.isIso_unit_app_iff_mem_essImage).mpr hA
  have := (a.isIso_unit_app_iff_mem_essImage).mpr hB
  have : IsIso (f ≫ a.unit.app B) := by
    change IsIso ((𝟭 C).map f ≫ a.unit.app B)
    rw [a.unit.naturality f]
    change IsIso (a.unit.app A ≫ R.map (L.map f))
    infer_instance
  exact IsIso.of_isIso_comp_right _ (a.unit.app B)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
-- The transported overlap restriction requires additional instance search.
-- Its derived adjunction and comparison need a larger elaboration budget.

/-- For a map from the direct image from P to one from W = O ∩ P, invertibility
on W implies invertibility on O. This applies to every such map, independently
of any choice of adjunction or of any formula for a mate.
Source: Stacks Project, Tag 08FE and the local identification in Tag 08DG.
(blueprint: lem-sc-derived-open-intersection-iso-detection).

Proof: Let k : W → O be the inclusion. By Tag 08FE, restriction to O of
RjP_* B is in the essential image of Rk_*: identify the inverse-image open
of O in P with W, and identify the induced morphism to O with k. Apply the
same result to jW and O; its inverse-image open is all of W, so restriction
to O of RjW_* C is also in the essential image of Rk_*. Let L be restriction
from O to W. The right adjoint Rk_* is fully faithful: underived open direct
image is fully faithful and preserves K-injectives because its left adjoint
is exact, so its total right derived functor is fully faithful. Consequently
L reflects isomorphisms between objects in this essential image. Explicitly,
the adjunction units at both objects are invertible, and naturality expresses
the given map as the conjugate of Rk_* applied to its L-restriction by these
units. The canonical nested-restriction comparison identifies that
L-restriction with restriction to W of the original map. The latter is
invertible by hypothesis, so the given map on O is invertible. No claim of
reflection on arbitrary objects of D(O) is made. If W is empty, both objects
on O are zero by the same Tag 08FE comparison. The argument also includes
O = X, P = X, and O ⊆ P without a covering assumption. -/
theorem derived_open_intersection_isIso_of_restriction
    (X : Scheme.{u}) (O P W : X.Opens) (hW : W = O ⊓ P)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings O.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings P.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (B : schemeDerivedCategory P.toScheme) (C : schemeDerivedCategory W.toScheme)
    (f : (schemeDerivedDirectImage P.ι).obj B ⟶ (schemeDerivedDirectImage W.ι).obj C)
    (hf : IsIso ((schemeOpenRestriction X W).mapDerivedCategory.map f)) :
    IsIso ((schemeOpenRestriction X O).mapDerivedCategory.map f) := by
  let iO : W ⟶ O := homOfLE (hW ▸ inf_le_left)
  let k := X.homOfLE (leOfHom iO)
  let e : schemeOpenOverlapRestriction X iO ≅ Scheme.Modules.restrictFunctor k :=
    Functor.isoWhiskerLeft (Scheme.Modules.overEquiv O).inverse
        (Scheme.Modules.overMapCompOverEquiv iO) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.overEquiv O).counitIso _ ≪≫
      Functor.leftUnitor _
  let a : schemeOpenOverlapRestriction X iO ⊣
      RingedSpace.moduleDirectImage k.toLRSHom.toShHom :=
    (Scheme.Modules.restrictAdjunction k).ofNatIsoLeft e.symm
  let adj := a.mapDerivedCategoryRightDerivedAdjunction
  have : (RingedSpace.moduleDirectImage k.toLRSHom.toShHom).Full :=
    (Scheme.Modules.restrictAdjunction k).fullyFaithfulROfIsIsoCounit.full
  have : (RingedSpace.moduleDirectImage k.toLRSHom.toShHom).Faithful :=
    (Scheme.Modules.restrictAdjunction k).fullyFaithfulROfIsIsoCounit.faithful
  have : (RingedSpace.moduleDirectImage k.toLRSHom.toShHom).PreservesKInjectiveComplexes :=
    a.preservesKInjectiveComplexes
  let rO := (schemeOpenRestriction X O).mapDerivedCategory
  have hA := derived_open_intersection_mem_essImage X O P W hW iO _ adj B
  have hB := derived_open_intersection_mem_essImage X O W W
    (inf_eq_right.mpr (leOfHom iO)).symm iO _ adj C
  have hmap : IsIso
      ((schemeOpenOverlapRestriction X iO).mapDerivedCategory.map (rO.map f)) := by
    exact (NatIso.isIso_map_iff (schemeDerivedOpenRestrictionCompIso X iO) f).mpr hf
  exact reflects_on_essential_image adj (rO.map f) hA hB hmap

end AlgebraicGeometry
