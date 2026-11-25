/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeTopRestrictionAux
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # Explicit inverse-image open comparison

Source: Stacks Project, Cohomology, Tags 08HZ and 08HY, and Schemes, Tag 01JR.
(blueprint: lem-pc-relative-mv-inverse-open-iso).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace AlgebraicGeometry

variable [d : ∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Transport the open localization object along a specified isomorphism over X.
The unit of pullback along the isomorphism is invertible. The last comparison is
right-adjoint uniqueness for the composite adjunction, using the specified equality
of scheme morphisms. Source: Stacks, Tags 01JR, 079W and 08HZ.
(blueprint: lem-pc-relative-mv-inverse-open-iso). -/
@[irreducible] def relativeMVIsoOpenTransport {A B X : Scheme.{u}} (s : B ≅ A)
    (j : A ⟶ X) (p : B ⟶ X) (h : s.hom ≫ j = p)
    (K : schemeDerivedCategory X) :
    (schemeDerivedDirectImage j).obj ((derivedPullback j).obj K) ≅
      (schemeDerivedDirectImage p).obj ((derivedPullback p).obj K) := by
  let c := relativeMVComp s.hom j ≪≫
    eqToIso (congrArg (fun t : B ⟶ X ↦ derivedPullback t) h)
  have : IsIso (relativeMVAdj s.hom).unit :=
    standardSingleBaseChange_topRestriction_iso_pullback_unit s
  exact (schemeDerivedDirectImage j).mapIso
      (asIso ((relativeMVAdj s.hom).unit.app ((derivedPullback j).obj K))) ≪≫
    (schemeDerivedDirectImage s.hom ⋙ schemeDerivedDirectImage j).mapIso (c.app K) ≪≫
    ((((relativeMVAdj j).comp (relativeMVAdj s.hom)).ofNatIsoLeft c).rightAdjointUniq
      (relativeMVAdj p)).app ((derivedPullback p).obj K)

private theorem iso_open_transport_unit {A B X : Scheme.{u}} (s : B ≅ A)
    (j : A ⟶ X) (p : B ⟶ X) (h : s.hom ≫ j = p)
    (K : schemeDerivedCategory X) :
    (relativeMVAdj j).unit.app K ≫ (relativeMVIsoOpenTransport s j p h K).hom =
      (relativeMVAdj p).unit.app K := by
  let c := relativeMVComp s.hom j ≪≫
    eqToIso (congrArg (fun t : B ⟶ X ↦ derivedPullback t) h)
  let a := ((relativeMVAdj j).comp (relativeMVAdj s.hom)).ofNatIsoLeft c
  have hu := Adjunction.unit_rightAdjointUniq_hom_app a (relativeMVAdj p) K
  simpa only [a, c, relativeMVIsoOpenTransport, Iso.trans_hom, Functor.mapIso_hom,
    asIso_hom, Iso.app_hom, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc] using hu

/-- The localization comparison on X', before applying any further direct image.
Source: Stacks, Tags 01JR, 079W and 08HZ.
(blueprint: lem-pc-relative-mv-inverse-open-iso). -/
@[irreducible] def relativeMVInverseOpenLocalizationIso {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (W : X.Opens) (K' : schemeDerivedCategory X') :
    (schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).obj
        ((schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.obj K') ≅
      (schemeDerivedDirectImage (pullback.fst g' W.ι)).obj
        ((derivedPullback (pullback.fst g' W.ι)).obj K') :=
  (schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).mapIso
    (((mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ W)).leftAdjointUniq
      (relativeMVAdj (g' ⁻¹ᵁ W).ι)).app K') ≪≫
  relativeMVIsoOpenTransport (pullbackRestrictIsoRestrict g' W) (g' ⁻¹ᵁ W).ι
    (pullback.fst g' W.ι) (pullbackRestrictIsoRestrict_hom_ι g' W) K'

private theorem inverse_open_localization_unit {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (W : X.Opens) (K' : schemeDerivedCategory X') :
    (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ W)).unit.app K' ≫
      (relativeMVInverseOpenLocalizationIso g' W K').hom =
      (relativeMVAdj (pullback.fst g' W.ι)).unit.app K' := by
  simp only [relativeMVInverseOpenLocalizationIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, ← Category.assoc]
  rw [Adjunction.unit_leftAdjointUniq_hom_app, iso_open_transport_unit]

/-- The inverse-image open comparison is constructed, independent of f, K and the
object map in a base-change square. Source: Stacks, Tags 01JR, 08HZ and 08HY.
(blueprint: lem-pc-relative-mv-inverse-open-iso). -/
@[irreducible] def relativeMVInverseOpenIso {X X' S' : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (W : X.Opens) (K' : schemeDerivedCategory X') :
    (schemeDerivedDirectImage f').obj
        ((schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).obj
          ((schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.obj K')) ≅
      (schemeDerivedDirectImage (pullback.fst g' W.ι ≫ f')).obj
        ((derivedPullback (pullback.fst g' W.ι)).obj K') :=
  (schemeDerivedDirectImage f').mapIso (relativeMVInverseOpenLocalizationIso g' W K') ≪≫
  (relativeMVImageComp (pullback.fst g' W.ι) f').app
    ((derivedPullback (pullback.fst g' W.ι)).obj K')

/-- The explicit inverse-open comparison preserves the unit.
Source: Stacks Project, Tag 08HZ, and adjunction uniqueness.
(blueprint: lem-pc-relative-mv-inverse-open-iso).

Proof: Left-adjoint uniqueness sends the exact-open unit to the pullback unit.
The composite adjunction unit is the j unit followed by Rj of the iso-pullback
unit. Transport this adjunction along the pullback composition comparison and
the projection equality. Right-adjoint uniqueness sends its unit to the p unit.
Apply Rf' and its pinned direct-image composition comparison. -/
theorem relativeMVInverseOpenIso_unit {X X' S' : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (W : X.Opens) (K' : schemeDerivedCategory X') :
    (schemeDerivedDirectImage f').map
        ((mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ W)).unit.app K') ≫
      (relativeMVInverseOpenIso g' f' W K').hom =
      relativeMVUnit (pullback.fst g' W.ι) f' K' := by
  simp only [relativeMVInverseOpenIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    relativeMVUnit, ← Category.assoc, ← Functor.map_comp]
  rw [inverse_open_localization_unit]

omit d in
private theorem restricted_counit_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C ⥤ E} {R' : E ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R') (H : D ⥤ E) (c : L ⋙ H ≅ L') (K : C) :
    a.unit.app K ≫ a'.homEquiv _ _
        (c.inv.app (R.obj (L.obj K)) ≫ H.map (a.counit.app (L.obj K)) ≫ c.hom.app K) =
      a'.unit.app K := by
  rw [← a'.homEquiv_naturality_left, ← a'.homEquiv_id]
  apply congrArg (a'.homEquiv _ _)
  erw [c.inv.naturality_assoc (a.unit.app K)]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, Functor.id_obj]
  erw [a.left_triangle_components]
  rw [H.map_id, Category.id_comp, c.inv_hom_id_app]

omit d in
private theorem precomp_injective_of_restriction_isIso
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {A B : C} (i : A ⟶ B) [IsIso (L.map i)]
    {Z : D} {p q : B ⟶ R.obj Z} (h : i ≫ p = i ≫ q) : p = q := by
  apply (a.homEquiv _ _).symm.injective
  apply (cancel_epi (L.map i)).mp
  simpa only [← a.homEquiv_naturality_left_symm] using
    congrArg (a.homEquiv _ _).symm h

private noncomputable def exact_open_image_fullyFaithful
    (X : Scheme.{u}) (U : X.Opens) :
    (schemeDerivedDirectImage U.ι).FullyFaithful := by
  let G := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let a : schemeOpenRestriction X U ⊣ G :=
    (Scheme.Modules.restrictAdjunction U.ι).ofNatIsoLeft
      (Scheme.Modules.overFunctorEquiv U).symm
  have : G.PreservesKInjectiveComplexes := a.preservesKInjectiveComplexes
  have : G.Full := (Scheme.Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.full
  have : G.Faithful := (Scheme.Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.faithful
  exact Functor.FullyFaithful.ofFullyFaithful G.rightDerivedFunctor

private theorem exact_nested_map_unit_isIso (X : Scheme.{u}) {W U : X.Opens}
    (i : W ≤ U) (K : schemeDerivedCategory X) :
    IsIso ((schemeOpenRestriction X W).mapDerivedCategory.map
      ((mvOpenRestrictionAdjunction X U).unit.app K)) := by
  let a := mvOpenRestrictionAdjunction X U
  let ff := exact_open_image_fullyFaithful X U
  have : (schemeDerivedDirectImage U.ι).Full := ff.full
  have : (schemeDerivedDirectImage U.ι).Faithful := ff.faithful
  have : IsIso ((schemeOpenRestriction X U).mapDerivedCategory.map (a.unit.app K)) := by
    exact (NatIso.isIso_app_of_isIso (Functor.whiskerRight a.unit _)) K
  let c := schemeDerivedOpenRestrictionCompIso X (homOfLE i)
  apply (NatIso.isIso_map_iff c (a.unit.app K)).mp
  change IsIso ((schemeOpenOverlapRestriction X (homOfLE i)).mapDerivedCategory.map
    ((schemeOpenRestriction X U).mapDerivedCategory.map (a.unit.app K)))
  infer_instance

omit d in
private theorem normalized_restriction
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {K AU BU BW : C} {Z : D} (i : K ⟶ AU) [IsIso (L.map i)]
    (r : AU ⟶ R.obj Z) (b : BU ⟶ BW) (qU : AU ≅ BU) (qW : R.obj Z ≅ BW)
    (j : K ⟶ R.obj Z) (pU : K ⟶ BU) (pW : K ⟶ BW)
    (hr : i ≫ r = j) (huU : i ≫ qU.hom = pU) (huW : j ≫ qW.hom = pW)
    (hb : pU ≫ b = pW) : r ≫ qW.hom = qU.hom ≫ b := by
  apply (cancel_mono qW.inv).mp
  apply precomp_injective_of_restriction_isIso a i
  have heq : i ≫ (r ≫ qW.hom) = i ≫ (qU.hom ≫ b) := by
    calc
      _ = (i ≫ r) ≫ qW.hom := (Category.assoc _ _ _).symm
      _ = j ≫ qW.hom := congrArg (fun t ↦ t ≫ qW.hom) hr
      _ = pW := huW
      _ = pU ≫ b := hb.symm
      _ = (i ≫ qU.hom) ≫ b := congrArg (fun t ↦ t ≫ b) huU.symm
      _ = _ := Category.assoc _ _ _
  simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ qW.inv) heq

omit d in
private theorem map_comparison_restriction
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {AU AW BU BW : C} {CU CW : D}
    (r : AU ⟶ AW) (b : BU ⟶ BW) (qU : AU ≅ BU) (qW : AW ≅ BW)
    (cU : F.obj BU ≅ CU) (cW : F.obj BW ≅ CW)
    (h : r ≫ qW.hom = qU.hom ≫ b) :
    F.map r ≫ (F.mapIso qW ≪≫ cW).hom =
      (F.mapIso qU ≪≫ cU).hom ≫ (cU.inv ≫ F.map b ≫ cW.hom) := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc]
  rw [h, Functor.map_comp]

private theorem inverse_open_restriction_of_units
    {X S A B : Scheme.{u}} (f : X ⟶ S) {W U : X.Opens} (i : W ⟶ U)
    (pU : A ⟶ X) (pW : B ⟶ X) (k : B ⟶ A) (h : k ≫ pU = pW)
    (K : schemeDerivedCategory X)
    (qU : (schemeDerivedDirectImage U.ι).obj
      ((schemeOpenRestriction X U).mapDerivedCategory.obj K) ≅
      (schemeDerivedDirectImage pU).obj ((derivedPullback pU).obj K))
    (qW : (schemeDerivedDirectImage W.ι).obj
      ((schemeOpenRestriction X W).mapDerivedCategory.obj K) ≅
      (schemeDerivedDirectImage pW).obj ((derivedPullback pW).obj K))
    (huU : (mvOpenRestrictionAdjunction X U).unit.app K ≫ qU.hom =
      (relativeMVAdj pU).unit.app K)
    (huW : (mvOpenRestrictionAdjunction X W).unit.app K ≫ qW.hom =
      (relativeMVAdj pW).unit.app K)
    [IsIso ((schemeOpenRestriction X W).mapDerivedCategory.map
      ((mvOpenRestrictionAdjunction X U).unit.app K))] :
    (schemeDerivedDirectImage f).map
        (schemeDerivedOpenDirectImageRestriction X i
          (mvOpenRestrictionAdjunction X U) (mvOpenRestrictionAdjunction X W) K) ≫
      ((schemeDerivedDirectImage f).mapIso qW ≪≫ (relativeMVImageComp pW f).app _).hom =
    ((schemeDerivedDirectImage f).mapIso qU ≪≫ (relativeMVImageComp pU f).app _).hom ≫
      relativeMVRestriction k pU pW h f K := by
  let aU := mvOpenRestrictionAdjunction X U
  let aW := mvOpenRestrictionAdjunction X W
  let c : derivedPullback pU ⋙ derivedPullback k ≅ derivedPullback pW :=
    relativeMVComp k pU ≪≫ eqToIso (congrArg (fun t : B ⟶ X ↦ derivedPullback t) h)
  let b : (schemeDerivedDirectImage pU).obj ((derivedPullback pU).obj K) ⟶
      (schemeDerivedDirectImage pW).obj ((derivedPullback pW).obj K) :=
    (relativeMVAdj pW).homEquiv _ _
      (c.inv.app ((schemeDerivedDirectImage pU).obj ((derivedPullback pU).obj K)) ≫
        (derivedPullback k).map ((relativeMVAdj pU).counit.app
          ((derivedPullback pU).obj K)) ≫ c.hom.app K)
  let r := schemeDerivedOpenDirectImageRestriction X i aU aW K
  have hr : aU.unit.app K ≫ r = aW.unit.app K :=
    restricted_counit_unit aU aW (schemeOpenOverlapRestriction X i).mapDerivedCategory
      (schemeDerivedOpenRestrictionCompIso X i) K
  have hb : (relativeMVAdj pU).unit.app K ≫ b = (relativeMVAdj pW).unit.app K :=
    restricted_counit_unit (relativeMVAdj pU) (relativeMVAdj pW) (derivedPullback k) c K
  have hbase : r ≫ qW.hom = qU.hom ≫ b :=
    normalized_restriction aW (aU.unit.app K) r b qU qW (aW.unit.app K)
      ((relativeMVAdj pU).unit.app K) ((relativeMVAdj pW).unit.app K) hr huU huW hb
  unfold relativeMVRestriction
  exact map_comparison_restriction (schemeDerivedDirectImage f) r b qU qW
    ((relativeMVImageComp pU f).app _) ((relativeMVImageComp pW f).app _) hbase

/-- The explicit inverse-open comparison intertwines nested restriction.
Source: Stacks Project, Tags 08BV and 08HZ, restricted-counit construction.
(blueprint: lem-pc-relative-mv-inverse-open-iso).

Proof: Each restriction, exact or pinned, composed with its U unit is its W unit,
by naturality and the triangle identity. Both localization comparisons preserve
units. Compose the desired equality with the exact U unit; the two sides then
agree. Exact restriction to W sends that unit to an isomorphism, since restriction
to W factors through U and open direct image is fully faithful. Transpose after
composing with the inverse W comparison, and cancel the mapped U unit. Finally
apply Rf' and cancel the inverse direct-image comparison on U. -/
theorem relativeMVInverseOpenIso_restriction {X X' S' : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') {W U : X.Opens} (i : W ≤ U) (K' : schemeDerivedCategory X') :
    (schemeDerivedDirectImage f').map
        (schemeDerivedOpenDirectImageRestriction X'
          ((TopologicalSpace.Opens.map g'.base).map (homOfLE i))
          (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U))
          (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ W)) K') ≫
      (relativeMVInverseOpenIso g' f' W K').hom =
    (relativeMVInverseOpenIso g' f' U K').hom ≫
      relativeMVRestriction (relativeMVOpenLift g' i)
        (pullback.fst g' U.ι) (pullback.fst g' W.ι)
        (pullback.lift_fst _ _ _) f' K' := by
  have : IsIso ((schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.map
      ((mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U)).unit.app K')) :=
    exact_nested_map_unit_isIso X' (show g' ⁻¹ᵁ W ≤ g' ⁻¹ᵁ U from
      (TopologicalSpace.Opens.map g'.base).monotone i) K'
  unfold relativeMVInverseOpenIso
  exact inverse_open_restriction_of_units f'
    ((TopologicalSpace.Opens.map g'.base).map (homOfLE i))
    (pullback.fst g' U.ι) (pullback.fst g' W.ι) (relativeMVOpenLift g' i)
    (pullback.lift_fst _ _ _) K'
    (relativeMVInverseOpenLocalizationIso g' U K')
    (relativeMVInverseOpenLocalizationIso g' W K')
    (inverse_open_localization_unit g' U K') (inverse_open_localization_unit g' W K')

end AlgebraicGeometry
