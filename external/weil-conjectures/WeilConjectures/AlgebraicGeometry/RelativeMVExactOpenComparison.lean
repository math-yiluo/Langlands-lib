/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # Exact restriction versus pinned relative restriction on one open

Source: Stacks Project, Cohomology, Tags 08BV and 08HZ.
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

/-- The comparison on one open, constructed by uniqueness of left adjoints and
composition of direct images. Source: Stacks, Tags 08BV and 08HZ
(blueprint: lem-pc-relative-mv-exact-open-comparison). -/
def relativeMVExactOpenIso {X S : Scheme.{u}} (f : X ⟶ S) (W : X.Opens)
    (K : schemeDerivedCategory X) :
    (schemeDerivedDirectImage f).obj ((schemeDerivedDirectImage W.ι).obj
      ((schemeOpenRestriction X W).mapDerivedCategory.obj K)) ≅
    (schemeDerivedDirectImage (W.ι ≫ f)).obj ((derivedPullback W.ι).obj K) :=
  (schemeDerivedDirectImage f).mapIso ((schemeDerivedDirectImage W.ι).mapIso
    (((mvOpenRestrictionAdjunction X W).leftAdjointUniq (relativeMVAdj W.ι)).app K)) ≪≫
      (relativeMVImageComp W.ι f).app ((derivedPullback W.ι).obj K)

/-- The exact-open comparison carries the restriction unit to the pinned relative
unit. Source: Stacks, Tag 08HZ; uniqueness of left adjoints
(blueprint: lem-pc-relative-mv-exact-open-comparison). -/
theorem relativeMVExactOpenIso_unit {X S : Scheme.{u}} (f : X ⟶ S) (W : X.Opens)
    (K : schemeDerivedCategory X) :
    (schemeDerivedDirectImage f).map ((mvOpenRestrictionAdjunction X W).unit.app K) ≫
      (relativeMVExactOpenIso f W K).hom = relativeMVUnit W.ι f K := by
  simp only [relativeMVExactOpenIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
     relativeMVUnit, ← Category.assoc, ← Functor.map_comp]
  change (schemeDerivedDirectImage f).map
    ((mvOpenRestrictionAdjunction X W).unit.app K ≫
      (schemeDerivedDirectImage W.ι).map
        (((mvOpenRestrictionAdjunction X W).leftAdjointUniq
          (relativeMVAdj W.ι)).hom.app K)) ≫ _ = _
  rw [Adjunction.unit_leftAdjointUniq_hom_app]

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

/-- The exact-open comparison intertwines restriction along a single inclusion.

Source: Stacks Project, Cohomology, Tags 08BV and 08HZ, the restricted-counit
construction of the second Mayer--Vietoris arrow.
(blueprint: lem-pc-relative-mv-exact-open-comparison).

Proof: For any two adjunctions and a comparison L_U followed by H to L_W,
the map defined as the transpose of the restricted U counit has composite with
the U unit equal to the W unit. This follows by naturality of the comparison
and the U triangle identity. Apply this observation both to exact restrictions
and to pinned pullbacks. The uniqueness comparisons preserve their units, so
the exact restriction followed by the W uniqueness comparison and the U
uniqueness comparison followed by pinned restriction have equal composites
with the exact U unit. Restriction to W sends this U unit to an isomorphism:
open direct image is fully faithful, the U triangle identity makes restriction
to U of its unit invertible, and exact nested restriction factors restriction
to W through U. The W adjunction therefore makes precomposition by the U unit
injective for maps into its direct-image objects. Cancel that unit to identify
the maps. Apply Rf*, insert the composition comparisons on U and W, and cancel
the comparison on U against its inverse. Empty opens and W=U are included. -/
theorem relativeMVExactOpenIso_restriction {X S : Scheme.{u}} (f : X ⟶ S)
    {W U : X.Opens} (i : W ≤ U) (K : schemeDerivedCategory X) :
    (schemeDerivedDirectImage f).map
        (schemeDerivedOpenDirectImageRestriction X (homOfLE i)
          (mvOpenRestrictionAdjunction X U) (mvOpenRestrictionAdjunction X W) K) ≫
      (relativeMVExactOpenIso f W K).hom =
    (relativeMVExactOpenIso f U K).hom ≫
      relativeMVRestriction (X.homOfLE i) U.ι W.ι (Scheme.homOfLE_ι X i) f K := by
  let aU := mvOpenRestrictionAdjunction X U
  let aW := mvOpenRestrictionAdjunction X W
  let cU := aU.leftAdjointUniq (relativeMVAdj U.ι)
  let cW := aW.leftAdjointUniq (relativeMVAdj W.ι)
  let c := relativeMVComp (X.homOfLE i) U.ι ≪≫
    eqToIso (congrArg (fun t : W.toScheme ⟶ X ↦ derivedPullback t) (Scheme.homOfLE_ι X i))
  let b := (relativeMVAdj W.ι).homEquiv _ _
    (c.inv.app ((schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K)) ≫
      (derivedPullback (X.homOfLE i)).map
        ((relativeMVAdj U.ι).counit.app ((derivedPullback U.ι).obj K)) ≫ c.hom.app K)
  let r := schemeDerivedOpenDirectImageRestriction X (homOfLE i) aU aW K
  have hr : aU.unit.app K ≫ r = aW.unit.app K := by
    exact restricted_counit_unit aU aW
      (schemeOpenOverlapRestriction X (homOfLE i)).mapDerivedCategory
      (schemeDerivedOpenRestrictionCompIso X (homOfLE i)) K
  have hb : (relativeMVAdj U.ι).unit.app K ≫ b = (relativeMVAdj W.ι).unit.app K :=
    restricted_counit_unit (relativeMVAdj U.ι) (relativeMVAdj W.ι)
      (derivedPullback (X.homOfLE i)) c K
  have hbase : r ≫ (schemeDerivedDirectImage W.ι).map (cW.hom.app K) =
      (schemeDerivedDirectImage U.ι).map (cU.hom.app K) ≫ b := by
    have : IsIso ((schemeOpenRestriction X W).mapDerivedCategory.map (aU.unit.app K)) :=
      exact_nested_map_unit_isIso X i K
    apply precomp_injective_of_restriction_isIso aW (aU.unit.app K)
    rw [← Category.assoc, hr, Adjunction.unit_leftAdjointUniq_hom_app,
      ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app, hb]
  change (schemeDerivedDirectImage f).map r ≫
      ((schemeDerivedDirectImage f).map ((schemeDerivedDirectImage W.ι).map
        (cW.hom.app K)) ≫ (relativeMVImageComp W.ι f).hom.app _) =
    ((schemeDerivedDirectImage f).map ((schemeDerivedDirectImage U.ι).map
        (cU.hom.app K)) ≫ (relativeMVImageComp U.ι f).hom.app _) ≫
      ((relativeMVImageComp U.ι f).inv.app _ ≫ (schemeDerivedDirectImage f).map b ≫
        (relativeMVImageComp W.ι f).hom.app _)
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc]
  rw [hbase, Functor.map_comp]


end AlgebraicGeometry
