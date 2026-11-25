/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.SupportedDerivedRestrictionZero
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Support and quasi-coherence of the open right-adjoint image

Source: Stacks Project, Tags 08D5, 08FE and 08BS.
(blueprint: lem-pc-supported-open-unit-image-properties).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact derived restriction has the original homology stalk at each point of the open.
Combine exact restriction/homology comparison with the over-site equivalence and
`Scheme.Modules.restrictStalkNatIso`. Source: Stacks Project, Tags 08DW and 06Z0. -/
private noncomputable def restrictionHomologyStalkIso
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (K : schemeDerivedCategory X) (n : ℤ) (x : U.toScheme) :
    TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj
        ((schemeOpenRestriction X U).mapDerivedCategory.obj K)).val.presheaf x ≅
    TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj K).val.presheaf x.val := by
  let H := Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor _ x
  let M := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K
  exact H.mapIso (((schemeOpenRestriction X U).mapDerivedCategoryHomologyFunctorIso n).symm.app K)
    ≪≫ H.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)
    ≪≫ (Scheme.Modules.restrictStalkNatIso U.ι x).app M

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Vanishing after open restriction implies vanishing of homology stalks on that open.
Apply homology and the additive stalk functor to the zero object, then use the stalk
comparison. Source: Stacks Project, Tag 05RU. -/
private theorem stalk_zero_of_restriction_zero
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (K : schemeDerivedCategory X)
    (hK : IsZero ((schemeOpenRestriction X U).mapDerivedCategory.obj K))
    (n : ℤ) (x : U.toScheme) :
    Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj K).val.presheaf x.val)) := by
  let H := Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor _ x
  have : (Scheme.Modules.toPresheaf U.toScheme).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hz := H.map_isZero ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).map_isZero hK)
  have hs := AddCommGrpCat.isZero_iff_subsingleton.mp hz
  let i := restrictionHomologyStalkIso X U K n x
  exact i.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp hs

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Open base change propagates cohomological support through derived direct image.
Restriction to the inverse image of the open complement of T is zero by supported
restriction. Open base change identifies restriction of the direct image with the
direct image of that zero object. Its homology stalks on the complement vanish.
Source: Stacks Project, Tags 08FE and 05RU. -/
private theorem direct_image_support
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : Y.Opens, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) (hT : IsClosed T) (K : schemeDerivedCategory Y)
    (hK : ∀ (n : ℤ) (y : Y), f y ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj K).val.presheaf y))) :
    ∀ (n : ℤ) (x : X), x ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj
        ((schemeDerivedDirectImage f).obj K)).val.presheaf x)) := by
  let O : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  let V := f ⁻¹ᵁ O
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings O.toScheme.toRingedSpace))
  have hz := supported_derived_restriction_zero Y (f ⁻¹' T) V
    (by intro y hy; exact hy) K hK
  let e := Scheme.Modules.overEquiv V
  have hres : IsZero ((schemeOpenRestriction Y V).mapDerivedCategory.obj K) := by
    let D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)
    let F : SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V) ⥤ D := e.functor
    have : F.Additive := Functor.additive_of_preserves_binary_products _
    have : PreservesFiniteLimits
        (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V ⋙ F) :=
      comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits
        (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V ⋙ F) :=
      comp_preservesFiniteColimits _ _
    exact (F.mapDerivedCategory.map_isZero hz).of_iso
      ((Functor.mapDerivedCategoryCompIso
        (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V)
        (Equivalence.functor (C := SheafOfModules.{u}
          ((moduleRings Y.toRingedSpace).over V)) (D := D) e)).symm.app K)
  obtain ⟨bc⟩ := schemeDerivedDirectImage_openRestriction f O
  have hout : IsZero ((schemeOpenRestriction X O).mapDerivedCategory.obj
      ((schemeDerivedDirectImage f).obj K)) := by
    exact ((schemeDerivedDirectImage (f ∣_ O)).map_isZero hres).of_iso (bc.app K)
  intro n x hx
  exact stalk_zero_of_restriction_zero X O _ hout n ⟨x, hx⟩

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The open right-adjoint image of a supported quasi-coherent complex remains supported
and quasi-coherent. This concerns the second vertex, with no cone or triangle supplied.
Source: Stacks Project, Tags 08D5 and 08FE; Tag 08BS for derived open adjunction.
(blueprint: lem-pc-supported-open-unit-image-properties).

Proof: Identify modules on the over-site with modules on the open subscheme using
Scheme.Modules.overEquiv U, and derive this exact equivalence. Exact restriction is
left adjoint to derived direct image: direct image preserves K-injectives because its
left adjoint is exact. Compose this adjunction with the derived equivalence, then use
uniqueness of right adjoints to identify the supplied R with that composite.
Restriction preserves quasi-coherent cohomology by exactness and local presentations.
The open immersion U to X is quasi-compact: in a quasi-separated scheme the intersection
of the compact open U with every compact affine open is compact. It is separated.
Thus derived direct image preserves quasi-coherent cohomology by Tag 08D5; transport
along the right-adjoint comparison gives quasi-coherence of R(L(K)).
For support, let O be the open complement of the closed set T. The support hypothesis
and supported_derived_restriction_zero give K restricted to O zero. Its further
restriction to U intersect O is zero. Open base change (Tag 08FE) identifies the
restriction of R(L(K)) to O with the derived direct image of this zero restriction.
An additive derived direct image sends zero to zero. Hence R(L(K)) restricts to zero
on O. Exact restriction commutes with homology; at each x in O its stalk is the
original homology stalk at x, which is therefore zero. Both conclusions transport
along the comparison isomorphism. No boundedness is needed. For empty U the image is
zero; for empty T the input and image are zero; for T = X the support clause is vacuous. -/
theorem supported_open_unit_image_properties
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (T : Set X) (hT : IsClosed T) (U : X.Opens) (hU : IsCompact (U : Set X))
    (R : DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
      schemeDerivedCategory X)
    (adj : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
    (K : schemeDerivedQCohCategory X)
    (hKT : ∀ (n : ℤ) (x : X), x ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
        K.obj).val.presheaf x))) :
    schemeDerivedQCohProperty X
      (R.obj ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K.obj)) ∧
    (∀ (n : ℤ) (x : X), x ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
        (R.obj ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K.obj))).val.presheaf x))) := by
  classical
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
  let (V : U.toScheme.Opens) := HasDerivedCategory.standard
    (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))
  let r := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Scheme.Modules.overEquiv U
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits (r ⋙ e.functor) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (r ⋙ e.functor) := comp_preservesFiniteColimits _ _
  let L := schemeOpenRestriction X U
  let G := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let a : L ⊣ G := (Scheme.Modules.restrictAdjunction U.ι).ofNatIsoLeft
    (Scheme.Modules.overFunctorEquiv U).symm
  let d := e.mapDerivedCategory
  let da : r.mapDerivedCategory ⋙ d.functor ⊣ G.rightDerivedFunctor :=
    a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
      (Functor.mapDerivedCategoryCompIso r e.functor).symm
  let ra : r.mapDerivedCategory ⊣ d.functor ⋙ G.rightDerivedFunctor :=
    (da.comp d.symm.toAdjunction).ofNatIsoLeft
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft r.mapDerivedCategory d.unitIso.symm ≪≫
        Functor.rightUnitor _)
  let α := ra.rightAdjointUniq adj
  let c : (schemeDerivedDirectImage U.ι).obj (L.mapDerivedCategory.obj K.obj) ≅
      R.obj (r.mapDerivedCategory.obj K.obj) :=
    G.rightDerivedFunctor.mapIso
      ((Functor.mapDerivedCategoryCompIso r e.functor).symm.app K.obj) ≪≫ α.app _
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have : QuasiCompact U.ι := quasiCompact_of_compactSpace U.ι
  have hres : schemeDerivedQCohProperty U.toScheme (L.mapDerivedCategory.obj K.obj) := by
    apply (schemeDerivedQCoh_openRestriction_iff X U K.obj).mpr
    intro n
    have := K.property n
    exact SheafOfModules.isQuasicoherent_over _ U
  have hpush := schemeDerivedDirectImage_preserves_QCoh U.ι _ hres
  refine ⟨?_, ?_⟩
  · intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso c) (hpush n)
  · have hlocal : ∀ (n : ℤ) (x : U.toScheme), U.ι x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk
          ((DerivedCategory.homologyFunctor _ n).obj
            (L.mapDerivedCategory.obj K.obj)).val.presheaf x)) := by
      intro n x hx
      let i := restrictionHomologyStalkIso X U K.obj n x
      exact i.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr (hKT n x.val hx)
    have hs := direct_image_support U.ι T hT (L.mapDerivedCategory.obj K.obj) hlocal
    intro n x hx
    let H := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor _ x
    let i := H.mapIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).mapIso c)
    exact i.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp (hs n x hx)

end AlgebraicGeometry
