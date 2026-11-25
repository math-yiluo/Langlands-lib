/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomOpenModuleMate
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate
import WeilConjectures.CategoryTheory.DerivedExactMateCompatibility
import WeilConjectures.AlgebraicGeometry.NormalizedDirectImageSquareUnit

/-! # Normalization of the open-square comparison on K-injective representatives

Source: Stacks Project, Cohomology, Tags 08FE, 08BS, 079W and 0D5S.
(blueprint: lem-pc-perfect-hom-open-mate-resolution-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

open CategoryTheory CategoryTheory.Limits

private theorem rotated_counit {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    {L : D ⥤ C} {R : C ⥤ D} {L' : D' ⥤ C'} {R' : C' ⥤ D'}
    {G : D ⥤ D'} {GR : D' ⥤ D} {H : C ⥤ C'} {HR : C' ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R') (ag : G ⊣ GR) (ah : H ⊣ HR)
    (k : G ⋙ L' ⟶ L ⋙ H) (theta : HR ⋙ R ⟶ R' ⋙ GR)
    (htheta : theta = conjugateEquiv (a.comp ah) (ag.comp a') k)
    (E : C) :
    L'.map (((mateEquiv ah ag).symm
      (TwoSquare.mk _ _ _ _ theta)).app E) ≫ a'.counit.app (H.obj E) =
        k.app (R.obj E) ≫ H.map (a.counit.app E) := by
  have hi := iterated_mateEquiv_conjugateEquiv a a' ag ah
    (TwoSquare.mk _ _ _ _ k)
  have hb : (mateEquiv ah ag).symm (TwoSquare.mk _ _ _ _ theta) =
      mateEquiv a a' (TwoSquare.mk _ _ _ _ k) := by
    apply (mateEquiv ah ag).injective
    rw [Equiv.apply_symm_apply]
    refine NatTrans.ext (funext fun X ↦ ?_)
    exact congr_app (htheta.trans hi.symm) X
  rw [hb]
  exact mateEquiv_counit a a' (TwoSquare.mk _ _ _ _ k) E

private theorem conjugate_open_transport {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    {L : D ⥤ C} {R : C ⥤ D} {L' : D' ⥤ C'} {R' : C' ⥤ D'}
    {G G₀ : D ⥤ D'} {GR : D' ⥤ D} {H H₀ : C ⥤ C'} {HR : C' ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R')
    (ag : G ⊣ GR) (ag₀ : G₀ ⊣ GR) (ah : H ⊣ HR) (ah₀ : H₀ ⊣ HR)
    (k : G ⋙ L' ⟶ L ⋙ H) :
    let sg := (conjugateIsoEquiv ag ag₀).symm (Iso.refl _)
    let sh := (conjugateIsoEquiv ah ah₀).symm (Iso.refl _)
    conjugateEquiv (a.comp ah₀) (ag₀.comp a')
      (Functor.whiskerRight sg.hom L' ≫ k ≫ Functor.whiskerLeft L sh.inv) =
        conjugateEquiv (a.comp ah) (ag.comp a') k := by
  dsimp only
  let sg := (conjugateIsoEquiv ag ag₀).symm (Iso.refl _)
  let sh := (conjugateIsoEquiv ah ah₀).symm (Iso.refl _)
  have hsg : conjugateEquiv ag ag₀ sg.hom = 𝟙 GR := by
    exact congrArg Iso.hom ((conjugateIsoEquiv ag ag₀).apply_symm_apply (Iso.refl GR))
  have hsh : conjugateEquiv ah₀ ah sh.inv = 𝟙 HR := by
    have hh := congrArg Iso.inv
      ((conjugateIsoEquiv ah ah₀).apply_symm_apply (Iso.refl HR))
    exact hh
  change conjugateEquiv (a.comp ah₀) (ag₀.comp a')
    (Functor.whiskerRight sg.hom L' ≫ k ≫ Functor.whiskerLeft L sh.inv) = _
  rw [← Category.assoc]
  rw [← conjugateEquiv_comp (a.comp ah₀) (a.comp ah) (ag₀.comp a')]
  rw [← conjugateEquiv_comp (a.comp ah) (ag.comp a') (ag₀.comp a')]
  rw [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft, hsg, hsh]
  simp

private theorem rotated_counit_transport {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    {L : D ⥤ C} {R : C ⥤ D} {L' : D' ⥤ C'} {R' : C' ⥤ D'}
    {G G₀ : D ⥤ D'} {GR : D' ⥤ D} {H H₀ : C ⥤ C'} {HR : C' ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R')
    (ag : G ⊣ GR) (ag₀ : G₀ ⊣ GR) (ah : H ⊣ HR) (ah₀ : H₀ ⊣ HR)
    (k : G ⋙ L' ⟶ L ⋙ H) (theta : HR ⋙ R ⟶ R' ⋙ GR)
    (m : R ⋙ G₀ ⟶ H₀ ⋙ R')
    (htheta : theta = conjugateEquiv (a.comp ah) (ag.comp a') k)
    (hm : m = ((mateEquiv ah₀ ag₀).symm (TwoSquare.mk _ _ _ _ theta)))
    (E : C) :
    let sg := (conjugateIsoEquiv ag ag₀).symm (Iso.refl _)
    let sh := (conjugateIsoEquiv ah ah₀).symm (Iso.refl _)
    L'.map (m.app E ≫ R'.map (sh.hom.app E)) ≫ a'.counit.app (H.obj E) =
      L'.map (sg.hom.app (R.obj E)) ≫ k.app (R.obj E) ≫ H.map (a.counit.app E) := by
  dsimp only
  let sg := (conjugateIsoEquiv ag ag₀).symm (Iso.refl _)
  let sh := (conjugateIsoEquiv ah ah₀).symm (Iso.refl _)
  let k₀ := Functor.whiskerRight sg.hom L' ≫ k ≫ Functor.whiskerLeft L sh.inv
  have ht₀ : theta = conjugateEquiv (a.comp ah₀) (ag₀.comp a') k₀ :=
    htheta.trans (conjugate_open_transport a a' ag ag₀ ah ah₀ k).symm
  have hh := rotated_counit a a' ag₀ ah₀ k₀ theta ht₀ E
  rw [← hm] at hh
  simp only [Functor.map_comp, Category.assoc]
  have hn := a'.counit.naturality (sh.hom.app E)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  change L'.map (m.app E) ≫ a'.counit.app (H₀.obj E) ≫ sh.hom.app E = _
  rw [← Category.assoc, hh]
  dsimp only [k₀, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  have hs := sh.hom.naturality (a.counit.app E)
  dsimp only [Functor.id_obj, Functor.comp_obj] at hs
  rw [hs]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

variable [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Derive the ordinary sectionwise comparison and identify exact open pullback
by uniqueness of left adjoints. All data are specified by functorial derivation
and adjunction uniqueness; the ordinary IsIso theorem determines only the inverse.
Source: Stacks Tags 08FE, 08BS, 079W
(blueprint: lem-pc-perfect-hom-open-mate-resolution-normalization). -/
def perfectHomOpenDerivedComparison {S Y T : Scheme.{u}}
    (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S) :
    schemeDerivedDirectImage (pullback.fst s r) ⋙ schemeMVDerivedRestriction Y B ≅
      derivedPullback (perfectHomOpenMap s B r) ⋙
        schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r) := by
  let : HasDerivedCategory.{w} (pullback s r).Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (pullback s r).toRingedSpace)))
  let : HasDerivedCategory.{w} (pullback (B.ι ≫ s) r).Modules := inferInstanceAs
    (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (pullback (B.ι ≫ s) r).toRingedSpace)))
  let : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let : HasDerivedCategory.{w} B.toScheme.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings B.toScheme.toRingedSpace)))
  have : IsGrothendieckAbelian.{u} (pullback s r).Modules :=
    SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u} (pullback (B.ι ≫ s) r).Modules :=
    SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u} Y.Modules :=
    SheafOfModules.isGrothendieckAbelian _
  have : Abelian.HasKInjectiveResolutions (pullback s r).Modules :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  have : Abelian.HasKInjectiveResolutions (pullback (B.ι ≫ s) r).Modules :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  have : Abelian.HasKInjectiveResolutions Y.Modules :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  let F := Scheme.Modules.pushforward (pullback.fst s r)
  let G := schemeOpenRestriction Y B
  let H := Scheme.Modules.restrictFunctor (perfectHomOpenMap s B r)
  let K := Scheme.Modules.pushforward (pullback.fst (B.ι ≫ s) r)
  have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits G := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits H :=
    (openImmersion_restriction_derived_properties (perfectHomOpenMap s B r)).1
  have : H.PreservesKInjectiveComplexes :=
    (openImmersion_restriction_derived_properties (perfectHomOpenMap s B r)).2
  have : F.Additive := inferInstance
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  have : H.Additive := inferInstance
  have : K.Additive := inferInstance
  have : (F ⋙ G).Additive := inferInstance
  have : (H ⋙ K).Additive := inferInstance
  have : IsIso (perfectHomOpenModuleMate s B r) := perfectHomOpenModuleMate_isIso s B r
  let aH : H.mapDerivedCategory ⊣ schemeDerivedDirectImage (perfectHomOpenMap s B r) :=
    (Scheme.Modules.restrictAdjunction (perfectHomOpenMap s B r))
      |>.mapDerivedCategoryRightDerivedAdjunction
  let σH : H.mapDerivedCategory ≅ derivedPullback (perfectHomOpenMap s B r) :=
    (conjugateIsoEquiv (canonicalPullbackAdjunction (perfectHomOpenMap s B r)) aH).symm
      (Iso.refl _)
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso.{w, w, w} F G).symm ≪≫
    Functor.rightDerivedFunctorNatIso.{u, u, u + 1, u + 1, w, w}
      (asIso (perfectHomOpenModuleMate s B r)) ≪≫
    Functor.rightDerivedFunctorCompIso.{u, u, u, u + 1, u + 1, u + 1, w, w, w} H K ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory.{w, w} H) _
      ≪≫ Functor.isoWhiskerRight σH _

/-- Transport the explicitly derived comparison to the supplied adjunctions.
The conjugations are isomorphisms determined by the identity of the left adjoints.
Source: Stacks Tag 079W and Mathlib's adjoint uniqueness
(blueprint: lem-pc-perfect-hom-open-mate-resolution-normalization). -/
def perfectHomOpenSuppliedComparison {S Y T : Scheme.{u}}
    (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (ap : derivedPullback (pullback.fst s r) ⊣
      schemeDerivedDirectImage (pullback.fst s r))
    (ap' : derivedPullback (pullback.fst (B.ι ≫ s) r) ⊣
      schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r)) :
    schemeDerivedDirectImage (pullback.fst s r) ⋙ schemeMVDerivedRestriction Y B ≅
      derivedPullback (perfectHomOpenMap s B r) ⋙
        schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r) :=
  let σ := (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
  let σ₀ := (conjugateIsoEquiv (canonicalPullbackAdjunction B.ι)
    (schemeMVAdjunction Y B)).symm (Iso.refl _)
  Functor.isoWhiskerRight
      ((conjugateIsoEquiv ap (canonicalPullbackAdjunction (pullback.fst s r)))
        (Iso.refl _)) (schemeMVDerivedRestriction Y B) ≪≫
    Functor.isoWhiskerLeft (schemeDerivedDirectImage (pullback.fst s r)) (σ ≪≫ σ₀.symm) ≪≫
    perfectHomOpenDerivedComparison s B r ≪≫
    Functor.isoWhiskerLeft (derivedPullback (perfectHomOpenMap s B r))
      ((conjugateIsoEquiv (canonicalPullbackAdjunction (pullback.fst (B.ι ≫ s) r)) ap')
        (Iso.refl _))

private local instance schemeDerivedInstance (Z : Scheme.{u}) :
    HasDerivedCategory.{w} Z.Modules :=
  inferInstanceAs (HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
private local instance schemeGrothendieckInstance (Z : Scheme.{u}) :
    IsGrothendieckAbelian.{u} Z.Modules :=
  SheafOfModules.isGrothendieckAbelian _
private local instance schemeKInjectiveInstance (Z : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions Z.Modules :=
  Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh

set_option linter.all false in
-- Avoid repeated lint traversal of fixed adjunction data after kernel checking.
set_option cleanup.letToHave false in
set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
-- Comparing fixed derived adjunctions requires extra instance conversion.
/-- On K-injective representatives the derived sectionwise comparison satisfies
the counit equation for the fixed pullback-composition comparison and canonical adjunctions.
Source: Stacks Project, Cohomology, `lemma-restrict-direct-image-open` (08FE),
`lemma-restrict-K-injective-to-open` (08BS), `lemma-adjoint` (079W), and
`lemma-derived-pullback-composition` (0D5S).
(blueprint: lem-pc-perfect-hom-open-mate-resolution-normalization).

Proof: First take the projection and open adjunctions pinned to the shared
left-derived counits and ordinary tensor adjunctions. Expand the derived
comparison into its exact-composition comparison, right derivation of the
ordinary open mate, K-injective-composition comparison, and exact-open
pullback identification. The right-derived unit factorization equations
identify these factors on I with the ordinary sectionwise comparison; open
restriction preserves K-injectivity by 08BS. The left-derived counit equation
for perfectHomComposition, evaluated on K-flat representatives, identifies
the inverse pullback square with the ordinary pullback-composition square.
Transpose that equation using the normalized derived Hom equivalences of
079W. On each open W of B both sides are the same map from sections on
pi inverse (B.ι image W), obtained by the ordinary tensor counit and
restriction. The equality of opens follows from the cartesian square.
Thus the maps of complexes coincide and localization gives the displayed
counit equation for the canonical adjunctions. No arbitrary adjunctions,
assertion about an arbitrary derived object, or invertibility of the derived
mate occurs in this obligation. Adjunction transport is proved separately
in the importing module. Empty and full opens and
the zero complex satisfy these same sectionwise equations. -/
theorem perfectHomOpenComparison_counit_resolution
    {S Y T : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (pullback s r).toRingedSpace)) ℤ)
    [I.IsKInjective] :
    let a := canonicalPullbackAdjunction B.ι
    let ap := canonicalPullbackAdjunction (pullback.fst s r)
    let ap' := canonicalPullbackAdjunction (pullback.fst (B.ι ≫ s) r)
    let b := perfectHomOpenMap s B r
    let σ : schemeMVDerivedRestriction Y B ≅ derivedPullback B.ι :=
      (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
    let he : b ≫ pullback.fst s r = pullback.fst (B.ι ≫ s) r ≫ B.ι := by
      simp [b, perfectHomOpenMap, pullback.map]
    let κ := perfectHomComposition b (pullback.fst s r) ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) he) ≪≫
      (perfectHomComposition (pullback.fst (B.ι ≫ s) r) B.ι).symm ≪≫
      Functor.isoWhiskerRight σ.symm (derivedPullback (pullback.fst (B.ι ≫ s) r))
    (derivedPullback (pullback.fst (B.ι ≫ s) r)).map
        ((perfectHomOpenDerivedComparison s B r).hom.app
          (DerivedCategory.Q.obj I)) ≫
        ap'.counit.app ((derivedPullback b).obj (DerivedCategory.Q.obj I)) =
      κ.inv.app ((schemeDerivedDirectImage (pullback.fst s r)).obj
        (DerivedCategory.Q.obj I)) ≫
        (derivedPullback b).map (ap.counit.app (DerivedCategory.Q.obj I)) := by
  let b := perfectHomOpenMap s B r
  let f := pullback.fst s r
  let f' := pullback.fst (B.ι ≫ s) r
  let F := Scheme.Modules.pushforward f
  let K := Scheme.Modules.pushforward f'
  let G := schemeOpenRestriction Y B
  let H := Scheme.Modules.restrictFunctor b
  let P := Scheme.Modules.pushforward b
  let Q := Scheme.Modules.pushforward B.ι
  let a := canonicalPullbackAdjunction f
  let a' : derivedPullback f' ⊣ K.rightDerivedFunctor := canonicalPullbackAdjunction f'
  let ag := canonicalPullbackAdjunction B.ι
  let ah := canonicalPullbackAdjunction b
  let ag₀ := schemeMVAdjunction Y B
  have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits G := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits H := (openImmersion_restriction_derived_properties b).1
  have : H.PreservesKInjectiveComplexes :=
    (openImmersion_restriction_derived_properties b).2
  have : F.Additive := inferInstance
  have : K.Additive := inferInstance
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  have : H.Additive := inferInstance
  let ah₀ : H.mapDerivedCategory ⊣ P.rightDerivedFunctor :=
    (Scheme.Modules.restrictAdjunction b).mapDerivedCategoryRightDerivedAdjunction
  let he : b ≫ f = f' ≫ B.ι := (perfectHomOpenSquare s B r).w.symm
  let k := perfectHomComposition f' B.ι ≪≫
    eqToIso (congrArg (fun t ↦ derivedPullback t) he.symm) ≪≫
    (perfectHomComposition b f).symm
  let ed := schemeNormalizedDirectImageCompIso b f ≪≫
    eqToIso (congrArg (fun t ↦ schemeDerivedDirectImage t) he) ≪≫
    (schemeNormalizedDirectImageCompIso f' B.ι).symm
  have ht : ed.hom = conjugateEquiv (a.comp ah) (ag.comp a') k.hom := by
    exact (derivedDirectImage_square_mate f f' B.ι b he).symm
  have : IsIso (perfectHomOpenModuleMate s B r) := perfectHomOpenModuleMate_isIso s B r
  have : PreservesFiniteColimits H := by
    have : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.restrictFunctor b) :=
      (Scheme.Modules.restrictAdjunction b).leftAdjoint_preservesColimits
    infer_instance
  have hu : Functor.rightDerivedFunctorCompUnit P F ≫
      Functor.whiskerLeft DerivedCategory.Qh ed.hom =
      Functor.whiskerRight
        (NatTrans.mapHomotopyCategory (perfectHomOpenModuleComposition s B r).hom (.up ℤ))
        DerivedCategory.Qh ≫ Functor.rightDerivedFunctorCompUnit K Q := by
    exact normalizedDirectImageSquare_unit f f' B.ι b he
  have hm : (Functor.exactMateComparison F K G H
      (asIso (perfectHomOpenModuleMate s B r))).hom =
      ((mateEquiv ah₀ ag₀).symm (TwoSquare.mk _ _ _ _ ed.hom)).natTrans := by
    exact Functor.exactMateComparison_eq F K G H P Q
      (Scheme.Modules.restrictAdjunction b) (schemeOpenModuleAdjunction Y B)
      (perfectHomOpenModuleComposition s B r) (asIso (perfectHomOpenModuleMate s B r))
      rfl ed hu
  have hh := rotated_counit_transport a a' ag ag₀ ah ah₀ k.hom ed.hom
    (Functor.exactMateComparison F K G H
      (asIso (perfectHomOpenModuleMate s B r))).hom ht hm (DerivedCategory.Q.obj I)
  dsimp only at hh ⊢
  simpa only [perfectHomOpenDerivedComparison,
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso_eq_viaRightDerived,
    Functor.exactMateComparison,
    k, F, K, G, H, P, Q, f, f', b, a, a', ag, ah, ag₀, ah₀,
    eqToIso.hom, eqToIso.inv, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Category.assoc] using hh

end
end AlgebraicGeometry
