/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import all WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement

/-! # Finite constant-ring section normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
attribute [local irreducible] SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
  CategoryTheory.constantSheaf Padic Padic.coefficientExtensionIntegers

namespace AlgebraicGeometry.ProEtale.SpTowerClasses
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtaleTensorComparison
open SheafOfModules
open scoped ChangeOfRings

private abbrev SiteRings (X : Scheme.{u}) := ProEtaleTensorComparison.Rings.{u} X

private abbrev SiteModules {X : Scheme.{u}} (R : SiteRings X) :=
  ProEtaleTensorComparison.Modules.{u} R

private local instance localRingSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) CommRingCat.{u + 1} :=
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  hasSheafifyEssentiallySmallSite _ _

private local instance modelContinuity {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleModelBaseChange.{u} f).IsContinuous
      (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
  proEtaleModelBaseChange_isContinuous.{u} f

private abbrev ringPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SiteRings.{u} Y ⥤ SiteRings.{u} X :=
  Scheme.proEtaleSheafInverseImage.{u, u + 2} f CommRingCat.{u + 1}

private abbrev ringAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ringPullback f ⊣ Scheme.proEtaleSheafDirectImage.{u, u + 2} f CommRingCat.{u + 1} :=
  Scheme.proEtaleSheafAdjunction.{u, u + 2} f CommRingCat.{u + 1}

private abbrev ScalarIsos {X : Scheme.{u}} {R S : SiteRings.{u} X} (c : R ≅ S) :=
  ∀ M : SiteModules.{u} R, changeOfRings.{u, u + 1, u + 1} c.hom M ≅
    (restrictScalars ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)).obj M

private abbrev ScalarNaturality {X : Scheme.{u}} {R S : SiteRings.{u} X} (c : R ≅ S)
    (theta : ScalarIsos c) :=
  ∀ (M N : SiteModules.{u} R) (k : M ⟶ N),
    changeOfRingsHom.{u, u + 1, u + 1} c.hom M k ≫ (theta N).hom =
      (theta M).hom ≫ (restrictScalars ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)).map k

private theorem scalarIso_exists {X : Scheme.{u}} {R S : SiteRings.{u} X} (c : R ≅ S) :
    ∃ theta : ∀ M : SiteModules.{u} R, changeOfRings.{u, u + 1, u + 1} c.hom M ≅
        (restrictScalars ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)).obj M,
      (∀ (M : SiteModules.{u} R) (U : X.ProEtᵒᵖ) (m : M.val.obj U),
        (theta M).inv.val.app U m =
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app
                (changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom M)).app U)
                  ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] m)) ∧
      (∀ (M N : SiteModules.{u} R) (k : M ⟶ N),
        changeOfRingsHom.{u, u + 1, u + 1} c.hom M k ≫ (theta N).hom =
          (theta M).hom ≫ (restrictScalars ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)).map k) := by
  obtain ⟨theta, _, hi, hn⟩ := exists_scalarExtensionRingIso.{u + 1, u, u + 1, u + 1} c
  dsimp only [changeOfRings, changeOfRingsOfUniverses,
    changeOfRingsPresheaf, changeOfRingsPresheafOfUniverses,
    changeOfRingsHom, changeOfRingsHomOfUniverses,
    scalarExtensionRingIsoTmul] at theta hi hn ⊢
  exact ⟨theta, hi, hn⟩

private def ringComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (R : SiteRings.{u} Y)
    (S : SiteRings.{u} X) (c : ProEtaleTensorComparison.inverseRing.{u} f R ≅ S) :
    (AlgebraicGeometry.ProEtale.setPullback f).obj (ProEtaleTensorComparison.ringSets.{u} R) ≅
      ProEtaleTensorComparison.ringSets.{u} S :=
  ringSetsIdentification f R ≪≫
    (sheafCompose (ProEt.topology X) (forget CommRingCat.{u + 1})).mapIso c

private theorem ringComparison_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (R : SiteRings.{u} Y)
    (S : SiteRings.{u} X) (c : ProEtaleTensorComparison.inverseRing.{u} f R ≅ S)
    (U : Y.ProEtᵒᵖ) (r : R.obj.obj U) :
    (ringComparison.{u} f R S c).hom.hom.app ((proEtaleBaseChange f).op.obj U)
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
          (ProEtaleTensorComparison.ringSets.{u} R)).hom.app U r) =
      c.hom.hom.app ((proEtaleBaseChange f).op.obj U)
        (((ringAdjunction.{u} f).unit.app R).hom.app U r) := by
  exact congrArg
    (fun z : (ProEtaleTensorComparison.inverseRing.{u} f R).obj.obj
        ((proEtaleBaseChange f).op.obj U) ↦
      c.hom.hom.app ((proEtaleBaseChange f).op.obj U) z)
    ((Classical.choose_spec (ringSetsIdentification_exists.{u} f R)).1 U.unop r)

private def moduleComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (R : SiteRings.{u} Y)
    (S : SiteRings.{u} X) (c : ProEtaleTensorComparison.inverseRing.{u} f R ≅ S)
    (theta : ScalarIsos c) (hn : ScalarNaturality c theta) :
    proEtaleRingModulePullback f R S c ⋙ SemilinearSections.underlying.{u + 1, u, u + 1}
        (ProEt.topology X) S ≅
      SemilinearSections.underlying.{u + 1, u, u + 1} (ProEt.topology Y) R ⋙
        AlgebraicGeometry.ProEtale.setPullback f := by
  let raw : SemilinearSections.underlying.{u + 1, u, u + 1} (ProEt.topology Y) R ⋙
      AlgebraicGeometry.ProEtale.setPullback f ≅
        ProEtaleTensorComparison.inverse.{u} f R ⋙
          SemilinearSections.underlying.{u + 1, u, u + 1} (ProEt.topology X)
            (ProEtaleTensorComparison.inverseRing.{u} f R) :=
    NatIso.ofComponents (fun M ↦ moduleSetsIdentification f M)
      (fun k ↦ ProEtaleTensorComparison.moduleSetsIdentification_naturality f k)
  let scal : proEtaleRingModulePullback f R S c ⋙
      SemilinearSections.underlying.{u + 1, u, u + 1} (ProEt.topology X) S ≅
        ProEtaleTensorComparison.inverse.{u} f R ⋙
          SemilinearSections.underlying.{u + 1, u, u + 1} (ProEt.topology X)
            (ProEtaleTensorComparison.inverseRing.{u} f R) :=
    NatIso.ofComponents (fun M ↦
      (SemilinearSections.underlying.{u + 1, u, u + 1} (ProEt.topology X) S).mapIso
        (theta ((ProEtaleTensorComparison.inverse.{u} f R).obj M))) (by
      intro M N k
      have h := congrArg
        (fun z ↦ (SemilinearSections.underlying.{u + 1, u, u + 1}
          (ProEt.topology X) S).map z)
        (hn _ _ ((ProEtaleTensorComparison.inverse.{u} f R).map k))
      simp only [Functor.map_comp] at h
      ext U m
      exact congrArg (fun z ↦ z.hom.app U m) h)
  exact scal ≪≫ raw.symm

private theorem moduleComparison_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (R : SiteRings.{u} Y)
    (S : SiteRings.{u} X) (c : ProEtaleTensorComparison.inverseRing.{u} f R ≅ S)
    (theta : ScalarIsos c) (hn : ScalarNaturality c theta)
    (M : SiteModules.{u} R) (U : Y.ProEtᵒᵖ) (m : M.val.obj U) :
    ((moduleComparison f R S c theta hn).inv.app M).hom.app
        ((proEtaleBaseChange f).op.obj U)
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
          (ProEtaleTensorComparison.moduleSets.{u} M)).hom.app U m) =
      (theta ((ProEtaleTensorComparison.inverse.{u} f R).obj M)).inv.val.app
        ((proEtaleBaseChange f).op.obj U) (inverseSection f M U.unop m) := by
  exact congrArg ((theta ((ProEtaleTensorComparison.inverse.{u} f R).obj M)).inv.val.app
    ((proEtaleBaseChange f).op.obj U))
      ((Classical.choose_spec (moduleSetsIdentification_exists f M)).1 U.unop m)

private def finiteInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y) (R : SiteRings.{u} Y)
    (S : SiteRings.{u} X) (c : ProEtaleTensorComparison.inverseRing.{u} f R ≅ S)
    (theta : ScalarIsos c) (hn : ScalarNaturality c theta) :
    AlgebraicInverseImage (AlgebraicGeometry.ProEtale.setPullback f) R S := by
  let eR := ringComparison.{u} f R S c
  let eM := moduleComparison f R S c theta hn
  have hr := ringComparison_unit f R S c
  have hm := moduleComparison_unit f R S c theta hn
  let ru (U : Y.ProEtᵒᵖ) : R.obj.obj U →+* S.obj.obj ((proEtaleBaseChange f).op.obj U) :=
    (c.hom.hom.app ((proEtaleBaseChange f).op.obj U)).hom.comp
      (((ringAdjunction.{u} f).unit.app R).hom.app U).hom
  refine {
    ringUnderlying := eR
    modules := proEtaleRingModulePullback f R S c
    moduleUnderlying := eM
    ringAdd := ?_
    ringMul := ?_
    ringZero := ?_
    ringOne := ?_
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_ }
  · intro T a b t ht
    exact ProEtaleTensorComparison.transport_binary f eR eR eR
      (fun U x y ↦ @Add.add (R.obj.obj U) inferInstance x y)
      (fun V x y ↦ @Add.add (S.obj.obj V) inferInstance x y)
      (fun i x y ↦ ((S.obj.map i).hom.map_add x y).symm)
      (by intro U x y; rw [hr, hr, hr]; exact (ru U).map_add x y) T a b t ht
  · intro T a b t ht
    exact ProEtaleTensorComparison.transport_binary f eR eR eR
      (fun U x y ↦ @Mul.mul (R.obj.obj U) inferInstance x y)
      (fun V x y ↦ @Mul.mul (S.obj.obj V) inferInstance x y)
      (fun i x y ↦ ((S.obj.map i).hom.map_mul x y).symm)
      (by intro U x y; rw [hr, hr, hr]; exact (ru U).map_mul x y) T a b t ht
  · intro T a ha
    exact ProEtaleTensorComparison.transport_binary f eR eR eR (fun U _ _ ↦ (0 : R.obj.obj U))
      (fun V _ _ ↦ (0 : S.obj.obj V))
      (fun i _ _ ↦ (S.obj.map i).hom.map_zero.symm)
      (by intro U x y; rw [hr]; exact (ru U).map_zero) T a a a ha
  · intro T a ha
    exact ProEtaleTensorComparison.transport_binary f eR eR eR (fun U _ _ ↦ (1 : R.obj.obj U))
      (fun V _ _ ↦ (1 : S.obj.obj V))
      (fun i _ _ ↦ (S.obj.map i).hom.map_one.symm)
      (by intro U x y; rw [hr]; exact (ru U).map_one) T a a a ha
  · intro M T a b t ht
    exact ProEtaleTensorComparison.transport_binary f
      (eM.app M).symm (eM.app M).symm (eM.app M).symm
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun V x y ↦ @Add.add
        (((proEtaleRingModulePullback f R S c).obj M).val.obj V) inferInstance x y)
      (fun i x y ↦
        ((((proEtaleRingModulePullback f R S c).obj M).val.map i).hom.map_add x y).symm)
      (by
        intro U x y
        erw [hm, hm, hm, ProEtaleTensorComparison.inverseSection_add]
        exact ((theta ((ProEtaleTensorComparison.inverse.{u} f R).obj M)).inv.val.app
          ((proEtaleBaseChange f).op.obj U)).hom.map_add _ _) T a b t ht
  · intro M T a ha
    exact ProEtaleTensorComparison.transport_binary f
      (eM.app M).symm (eM.app M).symm (eM.app M).symm
      (fun U _ _ ↦ (0 : M.val.obj U))
      (fun V _ _ ↦ (0 : ((proEtaleRingModulePullback f R S c).obj M).val.obj V))
      (fun i _ _ ↦
        (((proEtaleRingModulePullback f R S c).obj M).val.map i).hom.map_zero.symm)
      (by
        intro U x y
        erw [hm]
        have hz : inverseSection f M U.unop 0 = 0 := by
          exact (((SheafOfModules.pullbackPushforwardAdjunction
            (F := proEtaleModelBaseChange.{u} f)
            (J := proEtaleModelTopology Y) (K := proEtaleModelTopology X)
            (proEtaleModelRingUnit f R)).unit.app
              ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.app
                  (AsSmall.up.op.obj U)).hom.map_zero
        rw [hz]
        exact ((theta ((ProEtaleTensorComparison.inverse.{u} f R).obj M)).inv.val.app
          ((proEtaleBaseChange f).op.obj U)).hom.map_zero) T a a a ha
  · intro M T a b t ht
    exact ProEtaleTensorComparison.transport_binary f eR (eM.app M).symm (eM.app M).symm
      (fun U x y ↦ @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance x y)
      (fun V x y ↦ @SMul.smul (S.obj.obj V)
        (((proEtaleRingModulePullback f R S c).obj M).val.obj V) inferInstance x y)
      (fun i x y ↦
        (((proEtaleRingModulePullback f R S c).obj M).val.map_smul i x y).symm)
      (by
        intro U r m
        erw [hm, hr, hm, ProEtaleTensorComparison.inverseSection_smul]
        let V := (proEtaleBaseChange f).op.obj U
        let s := ((ringAdjunction.{u} f).unit.app R).hom.app U r
        have hs :=
          ((theta ((ProEtaleTensorComparison.inverse.{u} f R).obj M)).inv.val.app V).hom.map_smul
          (c.hom.hom.app V s) (inverseSection f M U.unop m)
        change (theta ((ProEtaleTensorComparison.inverse.{u} f R).obj M)).inv.val.app V
          (c.inv.hom.app V (c.hom.hom.app V s) • inverseSection f M U.unop m) = _ at hs
        rw [show c.inv.hom.app V (c.hom.hom.app V s) = s from
          ConcreteCategory.congr_hom (congrArg (fun q ↦ q.hom.app V) c.hom_inv_id) s] at hs
        exact hs) T a b t ht

private theorem ringComparison_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R R' : SiteRings.{u} Y} {S S' : SiteRings.{u} X}
    (c : ProEtaleTensorComparison.inverseRing.{u} f R ≅ S)
    (d : ProEtaleTensorComparison.inverseRing.{u} f R' ≅ S') (a : R ⟶ R') (b : S ⟶ S')
    (hc : (ringPullback.{u} f).map a ≫ d.hom = c.hom ≫ b) :
    (AlgebraicGeometry.ProEtale.setPullback f).map (ProEtaleTensorComparison.ringMapSets.{u} a) ≫
        (ringComparison.{u} f R' S' d).hom =
      (ringComparison.{u} f R S c).hom ≫ ProEtaleTensorComparison.ringMapSets.{u} b := by
  apply ProEtaleTensorComparison.inverseImage_map_ext f
  intro U r
  let eta := (AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit
  have ha := congrArg
    (fun z : ProEtaleTensorComparison.ringSets.{u} R ⟶ _ ↦ z.hom.app U r)
    (eta.naturality (ProEtaleTensorComparison.ringMapSets.{u} a))
  change (eta.app (ProEtaleTensorComparison.ringSets.{u} R')).hom.app U (a.hom.app U r) =
    ((AlgebraicGeometry.ProEtale.setPullback f).map
      (ProEtaleTensorComparison.ringMapSets.{u} a)).hom.app
      ((proEtaleBaseChange f).op.obj U)
        ((eta.app (ProEtaleTensorComparison.ringSets.{u} R)).hom.app U r) at ha
  change (ringComparison.{u} f R' S' d).hom.hom.app _
      (((AlgebraicGeometry.ProEtale.setPullback f).map
        (ProEtaleTensorComparison.ringMapSets.{u} a)).hom.app _
        ((eta.app (ProEtaleTensorComparison.ringSets.{u} R)).hom.app U r)) =
    b.hom.app _ ((ringComparison.{u} f R S c).hom.hom.app _
      ((eta.app (ProEtaleTensorComparison.ringSets.{u} R)).hom.app U r))
  rw [← ha, ringComparison_unit, ringComparison_unit]
  have hr := congrArg (fun z : R ⟶ _ ↦ z.hom.app U r)
    ((ringAdjunction.{u} f).unit.naturality a)
  change ((ringAdjunction.{u} f).unit.app R').hom.app U
      (a.hom.app U r) =
    ((ringPullback.{u} f).map a).hom.app
      ((proEtaleBaseChange f).op.obj U)
      (((ringAdjunction.{u} f).unit.app R).hom.app U r) at hr
  rw [hr]
  exact congrArg (fun z : ProEtaleTensorComparison.inverseRing.{u} f R ⟶ S' ↦
    z.hom.app ((proEtaleBaseChange f).op.obj U)
    (((ringAdjunction.{u} f).unit.app R).hom.app U r)) hc

private theorem finiteInverseImage_transpose {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : SiteRings.{u} Y) (S : SiteRings.{u} X)
    (c : ProEtaleTensorComparison.inverseRing.{u} f R ≅ S)
    (theta : ScalarIsos c) (hn : ScalarNaturality c theta)
    (hi : ∀ (M : SiteModules.{u} (ProEtaleTensorComparison.inverseRing.{u} f R))
      (U : X.ProEtᵒᵖ) (m : M.val.obj U),
      (theta M).inv.val.app U m =
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app
              (changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom M)).app U)
                ((1 : S.obj.obj U) ⊗ₜ[_,(c.hom.hom.app U).hom] m))
    (M : SiteModules.{u} R) (N : SiteModules.{u} S)
    (h : (proEtaleRingModulePullback f R S c).obj M ⟶ N) :
    (SemilinearSections.underlying.{u + 1, u, u + 1} (ProEt.topology Y) R).map
        ((proEtaleRingModuleAdjunction f R S c).homEquiv M N h) =
      (proEtaleSheafAdjunction f (Type (u + 1))).homEquiv _ _
        ((moduleComparison f R S c theta hn).inv.app M ≫
          (SemilinearSections.underlying.{u + 1, u, u + 1} (ProEt.topology X) S).map h) := by
  obtain ⟨g, hg, ht⟩ :=
    (Classical.choose_spec (proEtaleRingModuleAdjunction_existsUnique f R S c)).1 M N h
  ext U m
  change ((proEtaleRingModuleAdjunction f R S c).homEquiv M N h).val.app U m =
    h.val.app ((proEtaleBaseChange f).op.obj U)
      (((moduleComparison f R S c theta hn).inv.app M).hom.app
        ((proEtaleBaseChange f).op.obj U)
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
          (ProEtaleTensorComparison.moduleSets.{u} M)).hom.app U m))
  unfold proEtaleRingModuleAdjunction
  rw [moduleComparison_unit, hi, ht, Adjunction.homEquiv_unit]
  change g.val.app (AsSmall.up.op.obj ((proEtaleBaseChange f).op.obj U))
    (inverseSection f M U.unop m) = _
  exact hg _ _

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Finite-level inverse images in the constant quotient coordinates.
Source: Stacks 03D2 and 03D7; Zheng Construction 4.1; blueprint operations proof (2).
(blueprint: lem-sfb-tower-class-finite-section-inverse-images).

Proof: transport the algebraic ring and module inverse image through the canonical
constant-section coefficient comparison. Extension along this ring isomorphism
identifies its underlying module with inverse image on sets. The tensor insertion
map sends a section m to 1 tensor m; the inverse sends a tensor a tensor m to the
transported scalar action a times m. These maps respect tensor balancing and
sheafification and are inverse. Their graph equations give the algebraic lift.
Naturality of the constant-section comparison in the coefficient ring gives the
adjacent quotient equation. Use the specified tensor-insertion module adjunction
and the identity comparison for sectionwise pushforward. Its transpose evaluated
on m is the image of 1 tensor m, which is exactly the set-sheaf transpose.
The inverse-image functor, right adjoint and adjunction are retained as a single
package. This finite construction uses neither system functors nor derived
categories or tensor localizations. It includes empty schemes and n = 0. -/
theorem finite_sectionInverseImages {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ I : ∀ n, SheafOfModules.AlgebraicInverseImage
        (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
        (SpTowerShriek.B l E Y n) (SpTowerShriek.B l E X n),
    ∃ a : ∀ n, (I n).modules ⊣ Scheme.proEtaleConstantRingPushforward
        (SpTowerShriek.R l E n) f,
      (∀ n, (I n).modules =
        Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f) ∧
      (∀ n,
        (⟨(I n).modules, Scheme.proEtaleConstantRingPushforward
          (SpTowerShriek.R l E n) f, a n⟩ :
          Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n) ⥤
            SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n),
          Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n) ⥤
            SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n), L ⊣ P) =
        (⟨Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f,
          Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f,
          Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f⟩)) ∧
      (∀ n,
        (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map
            ((sheafCompose (Scheme.ProEt.topology Y)
              (CategoryTheory.forget CommRingCat.{u + 1})).map (SpTowerShriek.tau l E Y n)) ≫
            (I n).ringUnderlying.hom =
          (I (n + 1)).ringUnderlying.hom ≫
            (sheafCompose (Scheme.ProEt.topology X)
              (CategoryTheory.forget CommRingCat.{u + 1})).map (SpTowerShriek.tau l E X n)) ∧
      (∀ n (M : SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n))
        (N : SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n))
        (h : (I n).modules.obj M ⟶ N),
        (SemilinearSections.underlying.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).map
            ((a n).homEquiv M N h) =
          (Scheme.proEtaleSheafAdjunction f (Type (u + 1))).homEquiv _ _
            ((I n).moduleUnderlying.inv.app M ≫
              (SemilinearSections.underlying.{u + 1, u, u + 1}
                (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n)).map h)) := by
  classical
  let c (n : ℕ) := Scheme.proEtaleConstantRingComparison f (SpTowerShriek.R l E n)
  choose theta hi hn using fun n ↦ scalarIso_exists (c n)
  let I := fun n ↦ finiteInverseImage f (SpTowerShriek.B l E Y n)
    (SpTowerShriek.B l E X n) (c n) (theta n) (hn n)
  refine ⟨I, (fun n ↦ Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f),
    (fun n ↦ rfl), (fun n ↦ rfl), ?_, ?_⟩
  · intro n
    change (AlgebraicGeometry.ProEtale.setPullback f).map
        (ringMapSets (SpTowerShriek.tau l E Y n)) ≫
        (ringComparison.{u} f _ _ (c n)).hom =
      (ringComparison.{u} f _ _ (c (n + 1))).hom ≫ ringMapSets (SpTowerShriek.tau l E X n)
    apply ringComparison_naturality f
    simpa only [c, Scheme.proEtaleConstantRingComparison, asIso_hom, SpTowerShriek.tau,
      spCoefficientCommRings, Functor.ofOpSequence_map_homOfLE_succ] using
      Scheme.proEtaleConstantInverseImageMap_naturality f
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
            ULift.ringEquiv.toRingHom)))
  · intro n M N h
    exact finiteInverseImage_transpose f _ _ (c n) (theta n) (hn n) (hi n) M N h

end AlgebraicGeometry.ProEtale.SpTowerClasses
