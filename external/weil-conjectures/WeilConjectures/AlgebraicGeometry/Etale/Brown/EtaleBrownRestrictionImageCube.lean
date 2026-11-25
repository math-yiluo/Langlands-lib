/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
import all WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownRestrictionImageCubeCore
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownUnderlyingMate
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Assembly of the normalized restriction and image cube -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive
-- Expand components and cancel isomorphisms while all functors remain abstract.
private theorem normalized_cube_components
    {A B C D E F G H : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category F] [Category G] [Category H]
    (Dm : A ⥤ B) (Dn : C ⥤ D)
    (EmV : A ⥤ E) (EmW : B ⥤ F) (EnV : C ⥤ G) (EnW : D ⥤ H)
    (Gm : E ⥤ F) (Gn : G ⥤ H)
    (qV : A ⥤ C) (qW : B ⥤ D) (rV : E ⥤ G) (rW : F ⥤ H)
    (ρV : qV ⋙ EnV ≅ EmV ⋙ rV) (ρW : qW ⋙ EnW ≅ EmW ⋙ rW)
    (β : qV ⋙ Dn ≅ Dm ⋙ qW) (δ : rV ⋙ Gn ≅ Gm ⋙ rW)
    (ηm : Dm ⋙ EmW ⟶ EmV ⋙ Gm) (ηn : Dn ⋙ EnW ⟶ EnV ⋙ Gn)
    (h : Functor.whiskerLeft Dm ρW.hom ≫
        (Functor.whiskerRight ηm rW ≫ Functor.whiskerLeft EmV δ.inv) =
      (Functor.whiskerRight β.inv EnW ≫ Functor.whiskerLeft qV ηn) ≫
        Functor.whiskerRight ρV.hom Gn) :
    ∀ M : A, ηn.app (qV.obj M) ≫ Gn.map (ρV.hom.app M) ≫
        δ.hom.app (EmV.obj M) =
      EnW.map (β.hom.app M) ≫ ρW.hom.app (Dm.obj M) ≫ rW.map (ηm.app M) := by
  intro M
  have hh := congr_app h M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map] at hh
  simpa only [Category.assoc, Functor.mapIso_hom, Iso.app_hom] using
    rotate_iso_square (EnW.mapIso (β.app M)) (δ.app (EmV.obj M))
      (ηn.app (qV.obj M) ≫ Gn.map (ρV.hom.app M))
      (ρW.hom.app (Dm.obj M) ≫ rW.map (ηm.app M))
      (by simpa only [Category.assoc, Functor.mapIso_inv, Iso.app_inv] using hh)

section NormalizedCube
universe a av b bv c cv d dv da db dc dd
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{dc} C]
  {D : Type d} [Category.{dv} D] [Abelian D] [HasDerivedCategory.{dd} D]

-- Combine naturality and component rotation before any concrete specialization.
private theorem unit_normalized_cube_components
    [Abelian.HasKInjectiveResolutions A]
    (F₀ : A ⥤ B) (G₀ : C ⥤ D) [F₀.Additive] [G₀.Additive]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (GD : DerivedCategory C ⥤ DerivedCategory D)
    (u : F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ FD)
    (v : G₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ GD)
    (hu : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (u.app I))
    {I J K L : Type*} [Category I] [Category J] [Category K] [Category L]
    (Dn : I ⥤ J) (EmV : DerivedCategory A ⥤ K) (EmW : DerivedCategory B ⥤ L)
    (EnV : I ⥤ DerivedCategory C) (EnW : J ⥤ DerivedCategory D)
    (Gm : K ⥤ L) (qV : DerivedCategory A ⥤ I) (qW : DerivedCategory B ⥤ J)
    (rV : K ⥤ DerivedCategory C) (rW : L ⥤ DerivedCategory D)
    (ρV : qV ⋙ EnV ≅ EmV ⋙ rV) (ρW : qW ⋙ EnW ≅ EmW ⋙ rW)
    (β : qV ⋙ Dn ≅ FD ⋙ qW) (δ : rV ⋙ GD ≅ Gm ⋙ rW)
    (ηm : FD ⋙ EmW ⟶ EmV ⋙ Gm) (ηn : Dn ⋙ EnW ⟶ EnV ⋙ GD)
    (x x' : A ⥤ C) (y y' : B ⥤ D)
    [x.Additive] [x'.Additive] [y.Additive] [y'.Additive]
    (xf : DerivedCategory.Q ⋙ (qV ⋙ EnV) ≅
      x.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (xf' : DerivedCategory.Q ⋙ (EmV ⋙ rV) ≅
      x'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf : DerivedCategory.Q ⋙ (qW ⋙ EnW) ≅
      y.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf' : DerivedCategory.Q ⋙ (EmW ⋙ rW) ≅
      y'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : F₀ ⋙ y ⟶ x ⋙ G₀) (c' : F₀ ⋙ y' ⟶ x' ⋙ G₀)
    (hn : EtaleBrownUnitNorm F₀ G₀ FD GD u v x y (qV ⋙ EnV) (qW ⋙ EnW) xf yf c
      (Functor.whiskerRight β.inv EnW ≫ Functor.whiskerLeft qV ηn))
    (he : EtaleBrownUnitNorm F₀ G₀ FD GD u v x' y' (EmV ⋙ rV) (EmW ⋙ rW) xf' yf' c'
      (Functor.whiskerRight ηm rW ≫ Functor.whiskerLeft EmV δ.inv))
    (a : x ⟶ x') (d : y ⟶ y')
    (ha : ∀ P : CochainComplex A ℤ,
      ρV.hom.app (DerivedCategory.Q.obj P) ≫ xf'.hom.app P =
        xf.hom.app P ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex a (.up ℤ)).app P))
    (hd : ∀ P : CochainComplex B ℤ,
      ρW.hom.app (DerivedCategory.Q.obj P) ≫ yf'.hom.app P =
        yf.hom.app P ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex d (.up ℤ)).app P))
    (hc : ∀ M : A, d.app (F₀.obj M) ≫ c'.app M = c.app M ≫ G₀.map (a.app M)) :
    ∀ M : DerivedCategory A, ηn.app (qV.obj M) ≫ GD.map (ρV.hom.app M) ≫
        δ.hom.app (EmV.obj M) =
      EnW.map (β.hom.app M) ≫ ρW.hom.app (FD.obj M) ≫ rW.map (ηm.app M) := by
  exact normalized_cube_components FD Dn EmV EmW EnV EnW Gm GD
    qV qW rV rW ρV ρW β δ ηm ηn
    (etaleBrownNormalizedNaturality F₀ G₀ FD GD u v hu x x' y y'
      (qV ⋙ EnV) (EmV ⋙ rV) (qW ⋙ EnW) (EmW ⋙ rW) xf xf' yf yf' c c'
      (Functor.whiskerRight β.inv EnW ≫ Functor.whiskerLeft qV ηn)
      (Functor.whiskerRight ηm rW ≫ Functor.whiskerLeft EmV δ.inv)
      hn he a d ρV.hom ρW.hom ha hd hc)

end NormalizedCube

section FullCube
universe a av ad b bv bd c cv cd d dv dd e ev ed f fv fd g gv gd h hv hd
variable {A : Type a} [Category.{av} A] [Abelian A]
    [HasDerivedCategory.{ad} A]
  {B : Type b} [Category.{bv} B] [Abelian B]
    [HasDerivedCategory.{bd} B]
  {C : Type c} [Category.{cv} C] [Abelian C]
    [HasDerivedCategory.{cd} C]
  {D : Type d} [Category.{dv} D] [Abelian D]
    [HasDerivedCategory.{dd} D]
  {E : Type e} [Category.{ev} E] [Abelian E]
    [HasDerivedCategory.{ed} E]
  {F : Type f} [Category.{fv} F] [Abelian F]
    [HasDerivedCategory.{fd} F]
  {G : Type g} [Category.{gv} G] [Abelian G]
    [HasDerivedCategory.{gd} G]
  {H : Type h} [Category.{hv} H] [Abelian H]
    [HasDerivedCategory.{hd} H]

private theorem normalized_full_cube
    [Abelian.HasKInjectiveResolutions A]
    (fm : A ⥤ B) [fm.Additive]
    (fn : C ⥤ D) [fn.Additive]
    (gm : E ⥤ F) [gm.Additive]
    (gn : G ⥤ H) [gn.Additive]
    (qv : A ⥤ C) [qv.Additive]
    (qw : B ⥤ D) [qw.Additive]
    (emv : A ⥤ E) [emv.Additive]
    (emw : B ⥤ F) [emw.Additive]
    (env : C ⥤ G) [env.Additive]
    (enw : D ⥤ H) [enw.Additive]
    (rv : E ⥤ G) [rv.Additive]
    (rw : F ⥤ H) [rw.Additive]
    (FM : DerivedCategory A ⥤ DerivedCategory B)
    (FN : DerivedCategory C ⥤ DerivedCategory D)
    (GM : DerivedCategory E ⥤ DerivedCategory F)
    (GN : DerivedCategory G ⥤ DerivedCategory H)
    (QV : DerivedCategory A ⥤ DerivedCategory C)
    (QW : DerivedCategory B ⥤ DerivedCategory D)
    (EMV : DerivedCategory A ⥤ DerivedCategory E)
    (EMW : DerivedCategory B ⥤ DerivedCategory F)
    (ENV : DerivedCategory C ⥤ DerivedCategory G)
    (ENW : DerivedCategory D ⥤ DerivedCategory H)
    (RV : DerivedCategory E ⥤ DerivedCategory G)
    (RW : DerivedCategory F ⥤ DerivedCategory H)
    (ufm : fm.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ FM)
    (ufn : fn.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ FN)
    (ugm : gm.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ GM)
    (ugn : gn.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ GN)
    (hu : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (ufm.app I))
    (qvf : DerivedCategory.Q ⋙ QV ≅
      qv.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qwf : DerivedCategory.Q ⋙ QW ≅
      qw.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (emvf : DerivedCategory.Q ⋙ EMV ≅
      emv.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (emwf : DerivedCategory.Q ⋙ EMW ≅
      emw.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (envf : DerivedCategory.Q ⋙ ENV ≅
      env.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (enwf : DerivedCategory.Q ⋙ ENW ≅
      enw.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (rvf : DerivedCategory.Q ⋙ RV ≅
      rv.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (rwf : DerivedCategory.Q ⋙ RW ≅
      rw.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ρv : QV ⋙ ENV ≅ EMV ⋙ RV) (ρw : QW ⋙ ENW ≅ EMW ⋙ RW)
    (β : QV ⋙ FN ≅ FM ⋙ QW) (δ : RV ⋙ GN ≅ GM ⋙ RW)
    (ηm : FM ⋙ EMW ⟶ EMV ⋙ GM) (ηn : FN ⋙ ENW ⟶ ENV ⋙ GN)
    (α : fm ⋙ qw ⟶ qv ⋙ fn) (ηm₀ : fm ⋙ emw ⟶ emv ⋙ gm)
    (ηn₀ : fn ⋙ enw ⟶ env ⋙ gn) (δ₀ : gm ⋙ rw ⟶ rv ⋙ gn)
    (hq : EtaleBrownUnitNorm fm fn FM FN ufm ufn qv qw QV QW qvf qwf α β.inv)
    (hm : EtaleBrownUnitNorm fm gm FM GM ufm ugm emv emw EMV EMW emvf emwf ηm₀ ηm)
    (hn : EtaleBrownUnitNorm fn gn FN GN ufn ugn env enw ENV ENW envf enwf ηn₀ ηn)
    (hr : EtaleBrownUnitNorm gm gn GM GN ugm ugn rv rw RV RW rvf rwf δ₀ δ.inv)
    (a : qv ⋙ env ≅ emv ⋙ rv) (d : qw ⋙ enw ≅ emw ⋙ rw)
    (ha : ∀ I : CochainComplex A ℤ,
      ρv.hom.app (DerivedCategory.Q.obj I) ≫ RV.map (emvf.hom.app I) ≫
          rvf.hom.app ((emv.mapHomologicalComplex (.up ℤ)).obj I) =
        ENV.map (qvf.hom.app I) ≫
          envf.hom.app ((qv.mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app I))
    (hd : ∀ I : CochainComplex B ℤ,
      ρw.hom.app (DerivedCategory.Q.obj I) ≫ RW.map (emwf.hom.app I) ≫
          rwf.hom.app ((emw.mapHomologicalComplex (.up ℤ)).obj I) =
        ENW.map (qwf.hom.app I) ≫
          enwf.hom.app ((qw.mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex d (.up ℤ)).hom.app I))
    (hc : ∀ M : A,
      d.hom.app (fm.obj M) ≫
          (Functor.whiskerRight ηm₀ rw ≫ Functor.whiskerLeft emv δ₀).app M =
        (Functor.whiskerRight α enw ≫ Functor.whiskerLeft qv ηn₀).app M ≫
          gn.map (a.hom.app M)) :
    ∀ M : DerivedCategory A,
      ηn.app (QV.obj M) ≫ GN.map (ρv.hom.app M) ≫ δ.hom.app (EMV.obj M) =
        ENW.map (β.hom.app M) ≫ ρw.hom.app (FM.obj M) ≫ RW.map (ηm.app M) := by
  have hN := normalized_composition fm fn gn FM FN GN ufm ufn ugn
    qv qw env enw QV QW ENV ENW qvf qwf envf enwf α ηn₀ β.inv ηn hq hn
  have hS := normalized_composition fm gm gn FM GM GN ufm ugm ugn
    emv emw rv rw EMV EMW RV RW emvf emwf rvf rwf ηm₀ δ₀ ηm δ.inv hm hr
  have hA := pasted_factors_naturality qv emv env rv QV EMV ENV RV
    qvf emvf envf rvf a ρv ha
  have hD := pasted_factors_naturality qw emw enw rw QW EMW ENW RW
    qwf emwf enwf rwf d ρw hd
  exact unit_normalized_cube_components fm gn FM GN ufm ugn hu
    FN EMV EMW ENV ENW GM QV QW RV RW ρv ρw β δ ηm ηn
    (qv ⋙ env) (emv ⋙ rv) (qw ⋙ enw) (emw ⋙ rw)
    _ _ _ _ _ _ hN hS a.hom d.hom hA hD hc

end FullCube

-- Expose the localization equation without unfolding the whole coherence package.
private theorem brown_restriction_factors
    (O : Type (u + 1)) [CommRing O] (t : O) (V : Scheme.{u})
    (P : StrictEtaleEvaluation V O t) (R : StrictEtaleBrownRealization O t V P)
    {m n : ℕ} (h : m ≤ n) :
    let := R.val.ordinaryAdditive
    ∀ I : CochainComplex (strictEtaleLevel V O t m) ℤ,
      (R.val.restriction h).hom.app (DerivedCategory.Q.obj I) ≫
          (Sheaf.derivedRestrictScalars V.smallEtaleTopology
            (strictEtaleBrownRingMap O t h)).map ((R.val.factors m).hom.app I) ≫
          (Sheaf.restrictScalars V.smallEtaleTopology
            (strictEtaleBrownRingMap O t h)).mapDerivedCategoryFactors.hom.app
              (((strictEtaleBrownConstant O t V m).mapHomologicalComplex (.up ℤ)).obj I) =
        (R.val.derived n).map ((P.scalar h).restrictionFactors.hom.app I) ≫
          (R.val.factors n).hom.app
            (((coefficientRestriction (J := V.smallEtaleTopology) O t h).mapHomologicalComplex
              (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (R.val.ordinaryRestriction h) (.up ℤ)).hom.app I) :=
  R.property.2.1 h

/-- Exact scalar restriction commutes with the normalized Brown image square.
Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 07A4 and 0D6E.
(blueprint: lem-pur-brown-restriction-image-cube).
Proof: normalize the two composed squares on cochain representatives, using the
coefficient and geometric right-mate unit equations. The ordinary cube follows
by transposing its counit and evaluating sections. On a K-injective representative
the source derived unit is invertible, so the normalized ordinary cube implies
the derived cube. Transport across representative isomorphisms and cancel the
two restriction comparison isomorphisms. -/
theorem etaleBrownRestrictionImageCube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ n, StrictEtaleBrownImageRealization O t g n A (B.level n) RV RW)
    {m n : ℕ} (h : m ≤ n)
    (δ : Sheaf.derivedRestrictScalars V.smallEtaleTopology (strictEtaleBrownRingMap O t h) ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).rightDerivedFunctor ≅
      (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g).rightDerivedFunctor ⋙
        Sheaf.derivedRestrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (hδ : δ.inv = Etale.scalarRestrictionDirectImageMap (strictEtaleBrownRingMap O t h) g) :
    ∀ M : DerivedCategory (strictEtaleLevel V O t m),
      (rg n).right.hom.app ((PV.scalar h).restriction.obj M) ≫
          (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            g).rightDerivedFunctor.map ((RV.val.restriction h).hom.app M) ≫
          δ.hom.app ((RV.derived m).obj M) =
        (RW.derived n).map ((B.restrictedDirect h).hom.app M) ≫
          (RW.val.restriction h).hom.app ((B.level m).direct.obj M) ≫
          (Sheaf.derivedRestrictScalars W.smallEtaleTopology
            (strictEtaleBrownRingMap O t h)).map ((rg m).right.hom.app M) := by
  let := RV.val.ordinaryAdditive
  let := RW.val.ordinaryAdditive
  have : IsGrothendieckAbelian.{u + 1} (strictEtaleLevel V O t m) :=
    isGrothendieckAbelian_coefficientUniverse _
  have : Abelian.HasKInjectiveResolutions (strictEtaleLevel V O t m) := inferInstance
  exact normalized_full_cube (A.right m) (A.right n)
    (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g)
    (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
    (coefficientRestriction.{u + 1, u, u + 1} (J := V.smallEtaleTopology) O t h)
    (coefficientRestriction.{u + 1, u, u + 1} (J := W.smallEtaleTopology) O t h)
    (strictEtaleBrownConstant O t V m) (strictEtaleBrownConstant O t W m)
    (strictEtaleBrownConstant O t V n) (strictEtaleBrownConstant O t W n)
    (Sheaf.restrictScalars V.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (Sheaf.restrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (B.level m).direct (B.level n).direct
    (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g).rightDerivedFunctor
    (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).rightDerivedFunctor
    (PV.scalar h).restriction (PW.scalar h).restriction
    (RV.val.derived m) (RW.val.derived m) (RV.val.derived n) (RW.val.derived n)
    (Sheaf.derivedRestrictScalars V.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (B.level m).directUnit (B.level n).directUnit
    (rightUnitNT (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g))
    (rightUnitNT (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g))
    (B.level m).computes
    (PV.scalar h).restrictionFactors (PW.scalar h).restrictionFactors
    (RV.val.factors m) (RW.val.factors m) (RV.val.factors n) (RW.val.factors n)
    (Sheaf.restrictScalars V.smallEtaleTopology
      (strictEtaleBrownRingMap O t h)).mapDerivedCategoryFactors
    (Sheaf.restrictScalars W.smallEtaleTopology
      (strictEtaleBrownRingMap O t h)).mapDerivedCategoryFactors
    (RV.val.restriction h) (RW.val.restriction h) (B.restrictedDirect h) δ
    (rg m).right.hom (rg n).right.hom
    (mateEquiv (A.levelAdj m) (A.levelAdj n) (.mk _ _ _ _ (A.restrictInverse h).hom))
    (rg m).val.ordinaryRight.hom (rg n).val.ordinaryRight.hom
    (Etale.lowerStarRestrictScalarsIso (strictEtaleBrownRingMap O t h) g).hom
    (coefficient_right_normalized O t g A PW PV B h)
    (brown_image_normalized O t g A PW PV B RV RW rg m)
    (brown_image_normalized O t g A PW PV B RV RW rg n)
    (hδ.symm ▸ geometric_restriction_normalized (strictEtaleBrownRingMap O t h) g)
    (RV.val.ordinaryRestriction h) (RW.val.ordinaryRestriction h)
    (brown_restriction_factors O t V PV RV h) (brown_restriction_factors O t W PW RW h)
    (etaleBrownOrdinaryRestrictionCube O t g A PW PV B RV RW rg h)

end AlgebraicGeometry
