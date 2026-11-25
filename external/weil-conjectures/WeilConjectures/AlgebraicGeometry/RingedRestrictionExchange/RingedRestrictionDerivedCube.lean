/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.OpenCube.RingedRestrictionOpenCube
public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedExchangeChainUnit
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedRestrictionPullbackCube
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.AlgebraicGeometry.StrictTowerRingedSquare.ProEtaleRingedSquareLocalization

/-! # The derived exchange equation of a ringed restriction cube

## References

* Stacks Project, Tags 03CB, 09A5, 05S7 and 0E47
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance 30000]
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage
  proEtaleRingModuleAdjunction proEtaleCanonicalDerivedPullbackComparison
  StrictTowerRingedSquare.exchangeModuleSquare
variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

private abbrev pullSquare (r : StrictTowerRingedSquare sq) :
    (basePull r).mapDerivedCategory ⋙ (targetPull r).mapDerivedCategory ≅
      (verticalPull r).mapDerivedCategory ⋙ (upperPull r).mapDerivedCategory :=
  proEtaleAmbientRingedPullbackComparison sq r.RX r.RY r.RX' r.RY'
    r.cf r.cg r.cg' r.cf' r.coherent

variable {U : Scheme.{u}} {j : U ⟶ Y}

private theorem pullSquare_localization (r : StrictTowerRingedSquare sq) :
    pullSquare r = Functor.mapDerivedCategorySquareIso
      (F₁ := basePull r) (F₂ := targetPull r)
      (G₁ := verticalPull r) (G₂ := upperPull r) r.exchangeModuleSquare :=
  r.ambientSquare_localization

private theorem cube_base_localization (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j) :
    Functor.mapDerivedCategorySquareIso
      (F₁ := basePull C.sourceFace) (F₂ := basePull C.localRings)
      (G₁ := basePull r) (G₂ := basePull C.targetFace)
      C.baseFace.exchangeModuleSquare = pullSquare C.baseFace := by
  simpa only [basePull, targetPull, verticalPull, upperPull, OpenCube.sourceFace,
    OpenCube.targetFace, OpenCube.baseFace, OpenCube.upperFace] using
    (pullSquare_localization C.baseFace).symm

private theorem cube_target_localization (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j) :
    Functor.mapDerivedCategorySquareIso
      (F₁ := basePull C.targetFace) (F₂ := targetPull C.localRings)
      (G₁ := targetPull r) (G₂ := upperPull C.targetFace)
      C.targetFace.exchangeModuleSquare = pullSquare C.targetFace := by
  simpa only [basePull, targetPull, verticalPull, upperPull, OpenCube.sourceFace,
    OpenCube.targetFace, OpenCube.baseFace, OpenCube.upperFace] using
    (pullSquare_localization C.targetFace).symm

private theorem cube_source_localization (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j) :
    Functor.mapDerivedCategorySquareIso
      (F₁ := basePull C.sourceFace) (F₂ := verticalPull C.localRings)
      (G₁ := verticalPull r) (G₂ := upperPull C.sourceFace)
      C.sourceFace.exchangeModuleSquare = pullSquare C.sourceFace := by
  simpa only [basePull, targetPull, verticalPull, upperPull, OpenCube.sourceFace,
    OpenCube.targetFace, OpenCube.baseFace, OpenCube.upperFace] using
    (pullSquare_localization C.sourceFace).symm

private theorem cube_upper_localization (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j) :
    Functor.mapDerivedCategorySquareIso
      (F₁ := upperPull C.sourceFace) (F₂ := upperPull C.localRings)
      (G₁ := upperPull r) (G₂ := upperPull C.targetFace)
      C.upperFace.exchangeModuleSquare = pullSquare C.upperFace := by
  simpa only [basePull, targetPull, verticalPull, upperPull, OpenCube.sourceFace,
    OpenCube.targetFace, OpenCube.baseFace, OpenCube.upperFace] using
    (pullSquare_localization C.upperFace).symm

private theorem scheme_localized_cube (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j)
    (q1 : basePull C.sourceFace ⋙ basePull C.localRings ≅ basePull r ⋙ basePull C.targetFace)
    (q2 : basePull C.targetFace ⋙ targetPull C.localRings ≅ targetPull r ⋙ upperPull C.targetFace)
    (q3 : basePull r ⋙ targetPull r ≅ verticalPull r ⋙ upperPull r)
    (q4 : basePull C.localRings ⋙ targetPull C.localRings ≅
      verticalPull C.localRings ⋙ upperPull C.localRings)
    (q5 : basePull C.sourceFace ⋙ verticalPull C.localRings ≅
      verticalPull r ⋙ upperPull C.sourceFace)
    (q6 : upperPull C.sourceFace ⋙ upperPull C.localRings ≅ upperPull r ⋙ upperPull C.targetFace)
    (comm : ∀ M, (targetPull C.localRings).map (q1.hom.app M) ≫
      q2.hom.app ((basePull r).obj M) ≫ (upperPull C.targetFace).map (q3.hom.app M) =
      q4.hom.app ((basePull C.sourceFace).obj M) ≫ (upperPull C.localRings).map (q5.hom.app M) ≫
      q6.hom.app ((verticalPull r).obj M))
    (M : DerivedCategory (proEtaleRingModules Y r.RY)) :
    (targetPull C.localRings).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso q1).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso q2).hom.app ((basePull r).mapDerivedCategory.obj M) ≫
      (upperPull C.targetFace).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso q3).hom.app M) =
    (Functor.mapDerivedCategorySquareIso q4).hom.app
        ((basePull C.sourceFace).mapDerivedCategory.obj M) ≫
      (upperPull C.localRings).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso q5).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso q6).hom.app
        ((verticalPull r).mapDerivedCategory.obj M) := by
  have hcube := Functor.mapDerivedCategory_exactCube
    (basePull C.sourceFace) (basePull C.localRings) (targetPull C.localRings) (basePull r)
    (basePull C.targetFace) (targetPull r) (upperPull C.targetFace) (verticalPull r)
    (upperPull r) (verticalPull C.localRings) (upperPull C.localRings) (upperPull C.sourceFace)
    q1 q2 q3 q4 q5 q6 comm
  simpa only [Functor.mapDerivedCategorySquareIso, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app] using NatTrans.congr_app hcube M

private theorem pullSquare_cube (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j) (M : DerivedCategory (proEtaleRingModules Y r.RY)) :
    (targetPull C.localRings).mapDerivedCategory.map ((pullSquare C.baseFace).hom.app M) ≫
        (pullSquare C.targetFace).hom.app ((basePull r).mapDerivedCategory.obj M) ≫
        (upperPull C.targetFace).mapDerivedCategory.map ((pullSquare r).hom.app M) =
      (pullSquare C.localRings).hom.app ((basePull C.sourceFace).mapDerivedCategory.obj M) ≫
        (upperPull C.localRings).mapDerivedCategory.map
          ((pullSquare C.sourceFace).hom.app M) ≫
        (pullSquare C.upperFace).hom.app ((verticalPull r).mapDerivedCategory.obj M) := by
  have hcube := scheme_localized_cube r C
    C.baseFace.exchangeModuleSquare C.targetFace.exchangeModuleSquare r.exchangeModuleSquare
    C.localRings.exchangeModuleSquare C.sourceFace.exchangeModuleSquare
    C.upperFace.exchangeModuleSquare (restriction_pullback_cube r C) M
  simpa only [cube_base_localization, cube_target_localization,
    cube_source_localization, cube_upper_localization, ← pullSquare_localization] using hcube

private theorem normalized_mate_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (E : B)
    (e : R ⋙ G ⟶ H ⋙ S) (e' : R' ⋙ G' ⟶ H' ⋙ S')
    (mF : R ⋙ a ⟶ b ⋙ R') (mK : S ⋙ c ⟶ d ⋙ S')
    (he : (mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)) = e)
    (he' : (mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')) = e')
    (hF : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)) = mF)
    (hK : (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)) = mK) :
    c.map (e.app E) ≫ mK.app (H.obj E) ≫ S'.map (pH.hom.app E) =
      pG.hom.app (R.obj E) ≫ G'.map (mF.app E) ≫ e'.app (b.obj E) := by
  have h := exchangeMate_cube adj adjK adj' adjK' a b c d pF pG pH pK θ θ' hc E
  simpa only [he, he', hF, hK] using h

private theorem exchange_as_mate (r : StrictTowerRingedSquare sq) :
    (mateEquiv (proEtaleRingDerivedAdjunction f r.RY r.RX r.cf)
      (proEtaleRingDerivedAdjunction f' r.RY' r.RX' r.cf')
      (TwoSquare.mk _ _ _ _ (pullSquare r).hom)) = exchange r := by
  unfold exchange proEtaleAmbientRingedExchange pullSquare
  rfl

private theorem cube_source_mate (r : StrictTowerRingedSquare sq) (C : OpenCube r j) :
    (mateEquiv (proEtaleRingDerivedAdjunction f r.RY r.RX r.cf)
      (proEtaleRingDerivedAdjunction C.fU C.localRings.RY C.localRings.RX C.localRings.cf)
      (TwoSquare.mk _ _ _ _ (pullSquare C.sourceFace).hom)) =
        exchange C.sourceFace := by
  simpa only [OpenCube.sourceFace] using exchange_as_mate C.sourceFace

private theorem cube_target_mate (r : StrictTowerRingedSquare sq) (C : OpenCube r j) :
    (mateEquiv (proEtaleRingDerivedAdjunction f' r.RY' r.RX' r.cf')
      (proEtaleRingDerivedAdjunction C.fU' C.localRings.RY' C.localRings.RX'
        C.localRings.cf')
      (TwoSquare.mk _ _ _ _ (pullSquare C.targetFace).hom)) =
        exchange C.targetFace := by
  simpa only [OpenCube.targetFace] using exchange_as_mate C.targetFace

-- Give every face its shared-vertex type before applying the abstract mate theorem.
-- The construction contains only the already specified comparisons and adjunctions.
private structure TypedDerivedCube (r : StrictTowerRingedSquare sq) (C : OpenCube r j) where
  globalAdj : (verticalPull r).mapDerivedCategory ⊣
    (verticalPush r).rightDerivedFunctor
  targetAdj : (targetPull r).mapDerivedCategory ⊣
    (targetPush r).rightDerivedFunctor
  localAdj : (verticalPull C.localRings).mapDerivedCategory ⊣
    (verticalPush C.localRings).rightDerivedFunctor
  localTargetAdj : (targetPull C.localRings).mapDerivedCategory ⊣
    (targetPush C.localRings).rightDerivedFunctor
  sourceSquare : (basePull C.sourceFace).mapDerivedCategory ⋙
      (verticalPull C.localRings).mapDerivedCategory ≅
    (verticalPull r).mapDerivedCategory ⋙ (upperPull C.sourceFace).mapDerivedCategory
  baseSquare : (basePull C.sourceFace).mapDerivedCategory ⋙
      (basePull C.localRings).mapDerivedCategory ≅
    (basePull r).mapDerivedCategory ⋙ (basePull C.targetFace).mapDerivedCategory
  upperSquare : (upperPull C.sourceFace).mapDerivedCategory ⋙
      (upperPull C.localRings).mapDerivedCategory ≅
    (upperPull r).mapDerivedCategory ⋙ (upperPull C.targetFace).mapDerivedCategory
  targetSquare : (basePull C.targetFace).mapDerivedCategory ⋙
      (targetPull C.localRings).mapDerivedCategory ≅
    (targetPull r).mapDerivedCategory ⋙ (upperPull C.targetFace).mapDerivedCategory
  globalSquare : (basePull r).mapDerivedCategory ⋙ (targetPull r).mapDerivedCategory ≅
    (verticalPull r).mapDerivedCategory ⋙ (upperPull r).mapDerivedCategory
  localSquare : (basePull C.localRings).mapDerivedCategory ⋙
      (targetPull C.localRings).mapDerivedCategory ≅
    (verticalPull C.localRings).mapDerivedCategory ⋙ (upperPull C.localRings).mapDerivedCategory
  globalExchange : (verticalPush r).rightDerivedFunctor ⋙ (basePull r).mapDerivedCategory ⟶
    (upperPull r).mapDerivedCategory ⋙ (targetPush r).rightDerivedFunctor
  localExchange : (verticalPush C.localRings).rightDerivedFunctor ⋙
      (basePull C.localRings).mapDerivedCategory ⟶
    (upperPull C.localRings).mapDerivedCategory ⋙ (targetPush C.localRings).rightDerivedFunctor
  sourceExchange : (verticalPush r).rightDerivedFunctor ⋙
      (basePull C.sourceFace).mapDerivedCategory ⟶
    (upperPull C.sourceFace).mapDerivedCategory ⋙ (verticalPush C.localRings).rightDerivedFunctor
  targetExchange : (targetPush r).rightDerivedFunctor ⋙ (basePull C.targetFace).mapDerivedCategory ⟶
    (upperPull C.targetFace).mapDerivedCategory ⋙ (targetPush C.localRings).rightDerivedFunctor

@[irreducible] private def cube_data (r : StrictTowerRingedSquare sq) (C : OpenCube r j) :
    TypedDerivedCube r C where
  globalAdj := proEtaleRingDerivedAdjunction f r.RY r.RX r.cf
  targetAdj := proEtaleRingDerivedAdjunction f' r.RY' r.RX' r.cf'
  localAdj := proEtaleRingDerivedAdjunction C.fU C.localRings.RY C.localRings.RX C.localRings.cf
  localTargetAdj := proEtaleRingDerivedAdjunction C.fU' C.localRings.RY'
    C.localRings.RX' C.localRings.cf'
  sourceSquare := pullSquare C.sourceFace
  baseSquare := pullSquare C.baseFace
  upperSquare := pullSquare C.upperFace
  targetSquare := pullSquare C.targetFace
  globalSquare := pullSquare r
  localSquare := pullSquare C.localRings
  globalExchange := exchange r
  localExchange := exchange C.localRings
  sourceExchange := exchange C.sourceFace
  targetExchange := exchange C.targetFace

private theorem cube_data_coherent (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j) (M : DerivedCategory (proEtaleRingModules Y r.RY)) :
    (targetPull C.localRings).mapDerivedCategory.map (((cube_data r C).baseSquare).hom.app M) ≫
        ((cube_data r C).targetSquare).hom.app ((basePull r).mapDerivedCategory.obj M) ≫
        (upperPull C.targetFace).mapDerivedCategory.map (((cube_data r C).globalSquare).hom.app M) =
      ((cube_data r C).localSquare).hom.app ((basePull C.sourceFace).mapDerivedCategory.obj M) ≫
        (upperPull C.localRings).mapDerivedCategory.map
          (((cube_data r C).sourceSquare).hom.app M) ≫
        ((cube_data r C).upperSquare).hom.app ((verticalPull r).mapDerivedCategory.obj M) := by
  simpa only [cube_data] using pullSquare_cube r C M

private theorem cube_data_global_mate (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j) :
    (mateEquiv (cube_data r C).globalAdj (cube_data r C).targetAdj
      (TwoSquare.mk _ _ _ _ (cube_data r C).globalSquare.hom)) =
        (cube_data r C).globalExchange := by
  simpa only [cube_data] using exchange_as_mate r

private theorem cube_data_local_mate (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j) :
    (mateEquiv (cube_data r C).localAdj (cube_data r C).localTargetAdj
      (TwoSquare.mk _ _ _ _ (cube_data r C).localSquare.hom)) =
        (cube_data r C).localExchange := by
  simpa only [cube_data] using exchange_as_mate C.localRings

private theorem cube_data_source_mate (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j) :
    (mateEquiv (cube_data r C).globalAdj (cube_data r C).localAdj
      (TwoSquare.mk _ _ _ _ (cube_data r C).sourceSquare.hom)) =
        (cube_data r C).sourceExchange := by
  simpa only [cube_data] using cube_source_mate r C

private theorem cube_data_target_mate (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j) :
    (mateEquiv (cube_data r C).targetAdj (cube_data r C).localTargetAdj
      (TwoSquare.mk _ _ _ _ (cube_data r C).targetSquare.hom)) =
        (cube_data r C).targetExchange := by
  simpa only [cube_data] using cube_target_mate r C

private theorem typed_cube_exchange_comm (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j)
    (D : TypedDerivedCube r C)
    (hc : ∀ M : DerivedCategory (proEtaleRingModules Y r.RY),
    (targetPull C.localRings).mapDerivedCategory.map ((D.baseSquare).hom.app M) ≫
        (D.targetSquare).hom.app ((basePull r).mapDerivedCategory.obj M) ≫
        (upperPull C.targetFace).mapDerivedCategory.map ((D.globalSquare).hom.app M) =
      (D.localSquare).hom.app ((basePull C.sourceFace).mapDerivedCategory.obj M) ≫
        (upperPull C.localRings).mapDerivedCategory.map
          ((D.sourceSquare).hom.app M) ≫
        (D.upperSquare).hom.app ((verticalPull r).mapDerivedCategory.obj M))
    (hglobal :
    (mateEquiv D.globalAdj D.targetAdj
      (TwoSquare.mk _ _ _ _ D.globalSquare.hom)) =
        D.globalExchange)
    (hlocal :
    (mateEquiv D.localAdj D.localTargetAdj
      (TwoSquare.mk _ _ _ _ D.localSquare.hom)) =
        D.localExchange)
    (hsource :
    (mateEquiv D.globalAdj D.localAdj
      (TwoSquare.mk _ _ _ _ D.sourceSquare.hom)) =
        D.sourceExchange)
    (htarget :
    (mateEquiv D.targetAdj D.localTargetAdj
      (TwoSquare.mk _ _ _ _ D.targetSquare.hom)) =
        D.targetExchange)
    (K : DerivedCategory (proEtaleRingModules X r.RX)) :
    (basePull C.targetFace).mapDerivedCategory.map ((D.globalExchange).app K) ≫
        (D.targetExchange).app ((upperPull r).mapDerivedCategory.obj K) ≫
        (targetPush C.localRings).rightDerivedFunctor.map
          ((D.upperSquare).inv.app K) =
      (D.baseSquare).inv.app ((verticalPush r).rightDerivedFunctor.obj K) ≫
        (basePull C.localRings).mapDerivedCategory.map ((D.sourceExchange).app K) ≫
        (D.localExchange).app ((upperPull C.sourceFace).mapDerivedCategory.obj K) := by
  have h := @normalized_mate_cube
    (DerivedCategory (proEtaleRingModules Y r.RY))
    (DerivedCategory (proEtaleRingModules X r.RX))
    (DerivedCategory (proEtaleRingModules Y' r.RY'))
    (DerivedCategory (proEtaleRingModules X' r.RX'))
    (DerivedCategory (proEtaleRingModules U C.localRings.RY))
    (DerivedCategory (proEtaleRingModules C.XU C.localRings.RX))
    (DerivedCategory (proEtaleRingModules C.YU' C.localRings.RY'))
    (DerivedCategory (proEtaleRingModules C.XU' C.localRings.RX'))
    (instCategoryDerivedCategory _) (instCategoryDerivedCategory _)
    (instCategoryDerivedCategory _) (instCategoryDerivedCategory _)
    (instCategoryDerivedCategory _) (instCategoryDerivedCategory _)
    (instCategoryDerivedCategory _) (instCategoryDerivedCategory _)
    ((verticalPull r).mapDerivedCategory)
    ((verticalPush r).rightDerivedFunctor)
    ((basePull r).mapDerivedCategory)
    ((upperPull r).mapDerivedCategory)
    ((targetPull r).mapDerivedCategory)
    ((targetPush r).rightDerivedFunctor)
    ((verticalPull C.localRings).mapDerivedCategory)
    ((verticalPush C.localRings).rightDerivedFunctor)
    ((basePull C.localRings).mapDerivedCategory)
    ((upperPull C.localRings).mapDerivedCategory)
    ((targetPull C.localRings).mapDerivedCategory)
    ((targetPush C.localRings).rightDerivedFunctor)
    D.globalAdj D.targetAdj
    D.localAdj D.localTargetAdj
    (basePull C.sourceFace).mapDerivedCategory (upperPull C.sourceFace).mapDerivedCategory
    (basePull C.targetFace).mapDerivedCategory (upperPull C.targetFace).mapDerivedCategory
    D.sourceSquare.symm D.baseSquare.symm
    D.upperSquare.symm D.targetSquare.symm
    D.globalSquare.hom D.localSquare.hom
    (by simpa only [Iso.symm_inv] using hc) K
    D.globalExchange D.localExchange
    D.sourceExchange D.targetExchange
    (hglobal) (hlocal)
    (by simpa only [Iso.symm_inv] using hsource)
    (by simpa only [Iso.symm_inv] using htarget)
  simpa only [Iso.symm_hom, Iso.symm_inv] using h

private theorem cube_data_exchange_comm (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j)
    (K : DerivedCategory (proEtaleRingModules X r.RX)) :
    (basePull C.targetFace).mapDerivedCategory.map (((cube_data r C).globalExchange).app K) ≫
        ((cube_data r C).targetExchange).app ((upperPull r).mapDerivedCategory.obj K) ≫
        (targetPush C.localRings).rightDerivedFunctor.map
          (((cube_data r C).upperSquare).inv.app K) =
      ((cube_data r C).baseSquare).inv.app ((verticalPush r).rightDerivedFunctor.obj K) ≫
        (basePull C.localRings).mapDerivedCategory.map (((cube_data r C).sourceExchange).app K) ≫
        ((cube_data r C).localExchange).app
          ((upperPull C.sourceFace).mapDerivedCategory.obj K) := by
  exact typed_cube_exchange_comm r C (cube_data r C) (cube_data_coherent r C)
    (cube_data_global_mate r C) (cube_data_local_mate r C)
    (cube_data_source_mate r C) (cube_data_target_mate r C) K

/-- The six-face inverse-image cube yields the equation of derived exchange mates. -/
theorem restriction_exchange_cube (r : StrictTowerRingedSquare sq)
    (C : OpenCube r j)
    (K : DerivedCategory (proEtaleRingModules X r.RX)) :
    (basePull C.targetFace).mapDerivedCategory.map ((exchange r).app K) ≫
        (exchange C.targetFace).app ((upperPull r).mapDerivedCategory.obj K) ≫
        (targetPush C.localRings).rightDerivedFunctor.map
          ((proEtaleAmbientRingedPullbackComparison C.upperSquare
            C.upperFace.RX C.upperFace.RY C.upperFace.RX' C.upperFace.RY'
            C.upperFace.cf C.upperFace.cg C.upperFace.cg' C.upperFace.cf'
            C.upperFace.coherent).inv.app K) =
      (proEtaleAmbientRingedPullbackComparison C.baseSquare
            C.baseFace.RX C.baseFace.RY C.baseFace.RX' C.baseFace.RY'
            C.baseFace.cf C.baseFace.cg C.baseFace.cg' C.baseFace.cf'
            C.baseFace.coherent).inv.app ((verticalPush r).rightDerivedFunctor.obj K) ≫
        (basePull C.localRings).mapDerivedCategory.map ((exchange C.sourceFace).app K) ≫
        (exchange C.localRings).app ((upperPull C.sourceFace).mapDerivedCategory.obj K) := by
  simpa only [cube_data, pullSquare] using cube_data_exchange_comm r C K

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
