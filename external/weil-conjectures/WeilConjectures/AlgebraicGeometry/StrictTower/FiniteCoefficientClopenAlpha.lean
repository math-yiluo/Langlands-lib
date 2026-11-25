/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.StrictTower.MateEvaluationScalars.TowerMateEvaluationScalars
public import WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.StrictTower.MateEvaluationScalars.TowerMateEvaluationScalars
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import all WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenAlphaSiteTransport
import all WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenTailSiteTransport
import all WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows

/-! # The coefficient comparison for the clopen alpha

Source: Stacks Project, Tags 03DA, 099R, 09AF and 07A7; the first two steps of
lem-cbc-single-level-finite-proper-open-transport.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B Λ : Type (u + 1)) [CommRing B] [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)

/-- The ordinary inverse pullback comparison, with its specified inverse.
Source: Stacks Tags 03DA and 099R
(blueprint: lem-cbc-finite-coefficient-clopen-alpha). -/
def hPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    H B Y Λ φ ⋙ modulePullback B f ≅
      Etale.upperStar (ModuleCat.{u + 1} Λ) f ⋙ H B X Λ φ :=
  @asIso _ _ _ _ (hPullbackInv B f Λ φ) (hPullbackInv_isIso B f Λ φ)

/-- Exact descent of the inverse pullback comparison. Source: Stacks Tags 03DA and 07A7
(blueprint: lem-cbc-finite-coefficient-clopen-alpha). -/
def hPullbackPlus {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (H B Y Λ φ).mapDerivedCategoryPlus ⋙ (modulePullback B f).mapDerivedCategoryPlus ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (H B X Λ φ).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (hPullbackIso B Λ φ f) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- Exact descent of the forward extension-by-zero comparison. Source: Stacks Tag 09AF
(blueprint: lem-cbc-finite-coefficient-clopen-alpha). -/
def hOpenPlus {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus ⋙
        (H B X Λ φ).mapDerivedCategoryPlus ≅
      (H B U Λ φ).mapDerivedCategoryPlus ⋙ (moduleJ B j).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (@asIso _ _ _ _ (hOpen B j Λ φ) (hOpen_isIso B j Λ φ)) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

section CoefficientAlphaProof

open CategoryTheory.Limits Opposite MateEvaluationScalars
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

private def fcPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    C B Y Λ φ ⋙ modulePullback B f ≅
      upperStar (ModuleCat.{u + 1} Λ) f ⋙ C B X Λ φ :=
  @asIso _ _ _ _
    ((mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (openBetaModuleAdj B f)).symm
        (TwoSquare.mk _ _ _ _ (cDirect B f Λ φ).hom))
    (cPullback_isIso B f Λ φ)

private def fcOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    C B U Λ φ ⋙ moduleJ B j ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ⋙ C B X Λ φ :=
  @asIso _ _ _ _
    ((mateEquiv (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (moduleJAdj B j)).symm
        (TwoSquare.mk _ _ _ _ (fcPull B Λ φ j).inv))
    (cOpen_isIso B j Λ φ)

attribute [local irreducible] C fcPull fcOpen modulePullback
  Scheme.proEtaleRingModuleAdjunction Scheme.proEtaleRingModulePullback
  upperStar upperStarLowerStarAdjunction upperStarComp upperStarCompIso upperStarCongr

private lemma fcPull_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (openBetaModuleAdj B f) (fcPull B Λ φ f).hom =
        TwoSquare.mk _ _ _ _ (cDirect B f Λ φ).hom := by
  unfold fcPull
  exact (mateEquiv _ _).apply_symm_apply _

private lemma fcDirect_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (Y : Y.ProEtᵒᵖ)
    (m : ((C B _ Λ φ).obj
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).val.obj Y) :
    ((cUnderlying B X Λ φ).hom.app F).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj Y)
        (((cDirect B f Λ φ).hom.app F).val.app Y m) =
      ((cUnderlying B _ Λ φ).hom.app
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).hom.app Y m :=
  (Classical.choose_spec (cDirect_existsUnique B f Λ φ)).1 F Y m

private lemma fcUnderlying_map {X : Scheme.{u}}
    {F F' : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (h : F ⟶ F') (Y : X.ProEtᵒᵖ)
    (m : ((C B X Λ φ).obj F).val.obj Y) :
    ((cUnderlying B X Λ φ).hom.app F').hom.app Y
        (((C B X Λ φ).map h).val.app Y m) =
      h.hom.app Y (((cUnderlying B X Λ φ).hom.app F).hom.app Y m) := by
  have ht := (cUnderlying B X Λ φ).hom.naturality h
  exact ConcreteCategory.congr_hom (congr_app (congrArg
    (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map ht) Y) m

private lemma fcUnderlying_restrict {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    {Y Z : X.ProEtᵒᵖ} (h : Y ⟶ Z)
    (m : ((C B X Λ φ).obj F).val.obj Y) :
    ((cUnderlying B X Λ φ).hom.app F).hom.app Z
        (((C B X Λ φ).obj F).val.map h m) =
      F.obj.map h (((cUnderlying B X Λ φ).hom.app F).hom.app Y m) := by
  exact ConcreteCategory.congr_hom
    (((cUnderlying B X Λ φ).hom.app F).hom.naturality h) m

private lemma fcPull_compSquare {V W Z : Scheme.{u}}
    (f : V ⟶ W) (g : W ⟶ Z) :
    ((TwoSquare.mk _ _ _ _ (fcPull B Λ φ g).hom).vComp
      (TwoSquare.mk _ _ _ _ (fcPull B Λ φ f).hom)).whiskerRight
        (moduleGComp B f g).hom =
      (TwoSquare.mk _ _ _ _ (fcPull B Λ φ (f ≫ g)).hom).whiskerLeft
        (upperStarComp (ModuleCat.{u + 1} Λ) f g).hom := by
  let q := (TwoSquare.mk _ _ _ _ (fcPull B Λ φ g).hom).vComp
    (TwoSquare.mk _ _ _ _ (fcPull B Λ φ f).hom)
  have hc : q.whiskerRight (moduleGComp B f g).hom =
      (TwoSquare.mk _ _ _ _ (fcPull B Λ φ (f ≫ g)).hom).whiskerLeft
        (upperStarComp (ModuleCat.{u + 1} Λ) f g).hom := by
    apply finiteMateSquare
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f))
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (f ≫ g))
      ((openBetaModuleAdj B g).comp (openBetaModuleAdj B f))
      (openBetaModuleAdj B (f ≫ g))
    dsimp only [q]
    rw [mateEquiv_hcomp, fcPull_mate, fcPull_mate, fcPull_mate]
    have hm : conjugateEquiv ((openBetaModuleAdj B g).comp (openBetaModuleAdj B f))
        (openBetaModuleAdj B (f ≫ g)) (moduleGComp B f g).hom =
          (moduleRComp B f g).hom := by
      simpa only [moduleGComp, openBetaModuleAdj, modulePullback, moduleDirectImage,
        Modules, Iso.symm_hom] using!
        (Adjunction.conjugateEquiv_leftAdjointCompIso_inv
          (Scheme.proEtaleRingModuleAdjunction g (coefficients B Z)
            (coefficients B W) (constantRingIso B g))
          (Scheme.proEtaleRingModuleAdjunction f (coefficients B W)
            (coefficients B V) (constantRingIso B f))
          (Scheme.proEtaleRingModuleAdjunction (f ≫ g) (coefficients B Z)
            (coefficients B V) (constantRingIso B (f ≫ g))) (moduleRComp B f g))
    rw [hm]
    rw [conjugateEquiv_upperStarComp_hom]
    refine NatTrans.ext (funext fun N ↦ ?_)
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro Y
    ext n
    simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    apply (ConcreteCategory.bijective_of_isIso
      (((cUnderlying B V Λ φ).hom.app N).hom.app
        ((Scheme.proEtaleBaseChange (f ≫ g)).op.obj Y))).1
    obtain ⟨Y⟩ := Y
    erw [directComp_hom_apply f g B]
    erw [fcUnderlying_restrict]
    erw [directImage_map_apply g B, fcDirect_apply, fcDirect_apply,
      fcDirect_apply]
    erw [fcUnderlying_map, lowerStarComp_hom_app_hom_app]
    rfl
  exact hc

private lemma fcPull_square {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (w : a ≫ j = j' ≫ g)
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (moduleSquareG B a j' j g w).inv.app ((C B X Λ φ).obj N) ≫
      (modulePullback B j').map ((fcPull B Λ φ g).hom.app N) ≫
      (fcPull B Λ φ j').hom.app ((upperStar (ModuleCat.{u + 1} Λ) g).obj N) =
    (modulePullback B a).map ((fcPull B Λ φ j).hom.app N) ≫
      (fcPull B Λ φ a).hom.app ((upperStar (ModuleCat.{u + 1} Λ) j).obj N) ≫
      (C B U' Λ φ).map ((upperStarCompIso (ModuleCat.{u + 1} Λ) w).hom.app N) := by
  let p := (TwoSquare.mk _ _ _ _ (fcPull B Λ φ j).hom).vComp
    (TwoSquare.mk _ _ _ _ (fcPull B Λ φ a).hom)
  let p' := (TwoSquare.mk _ _ _ _ (fcPull B Λ φ g).hom).vComp
    (TwoSquare.mk _ _ _ _ (fcPull B Λ φ j').hom)
  have hw : upperStarCompIso (ModuleCat.{u + 1} Λ) w =
      (upperStarComp (ModuleCat.{u + 1} Λ) a j).symm ≪≫
      eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ)) w) ≪≫
      upperStarComp (ModuleCat.{u + 1} Λ) j' g := by
    simp only [upperStarCompIso, upperStarCongr]
  have hs := finiteSquareTransport (modulePullback B) (upperStar (ModuleCat.{u + 1} Λ))
    (C B X Λ φ) (C B U' Λ φ)
    (fun f ↦ TwoSquare.mk _ _ _ _ (fcPull B Λ φ f).hom) w
    (moduleGComp B a j) (moduleGComp B j' g)
    (upperStarComp (ModuleCat.{u + 1} Λ) a j)
    (upperStarComp (ModuleCat.{u + 1} Λ) j' g) p p'
    (fcPull_compSquare B Λ φ a j) (fcPull_compSquare B Λ φ j' g)
    (moduleSquareG B a j' j g w) (upperStarCompIso (ModuleCat.{u + 1} Λ) w)
    (moduleSquareG_eq B a j' j g w) hw
  exact finiteSquareComponents
    (C B X Λ φ) (C B U Λ φ)
    (C B X' Λ φ) (C B U' Λ φ)
    (upperStar (ModuleCat.{u + 1} Λ) j) (upperStar (ModuleCat.{u + 1} Λ) g)
    (upperStar (ModuleCat.{u + 1} Λ) a) (upperStar (ModuleCat.{u + 1} Λ) j')
    (modulePullback B j) (modulePullback B g) (modulePullback B a) (modulePullback B j')
    (fcPull B Λ φ j).hom (fcPull B Λ φ g).hom
    (fcPull B Λ φ a).hom (fcPull B Λ φ j').hom
    (moduleSquareG B a j' j g w) (upperStarCompIso (ModuleCat.{u + 1} Λ) w) hs N

private lemma fcOpen_mate {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    mateEquiv (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (moduleJAdj B j) (fcOpen B Λ φ j).hom =
        TwoSquare.mk _ _ _ _ (fcPull B Λ φ j).inv := by
  unfold fcOpen
  exact (mateEquiv _ _).apply_symm_apply _

private lemma fcOpen_cube {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g)
    (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ)) :
    (openBetaModule B a j' j g w sq).hom.app ((C B U Λ φ).obj M) ≫
      (moduleJ B j').map ((fcPull B Λ φ a).hom.app M) ≫
      (fcOpen B Λ φ j').hom.app ((upperStar (ModuleCat.{u + 1} Λ) a).obj M) =
    (modulePullback B g).map ((fcOpen B Λ φ j).hom.app M) ≫
      (fcPull B Λ φ g).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj M) ≫
      (C B X' Λ φ).map
        ((openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sq).inv.app M) := by
  exact finiteMateCube
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j')
    (moduleJAdj B j) (moduleJAdj B j')
    (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sq)
    (openBetaModule B a j' j g w sq)
    (fcOpen B Λ φ j) (fcOpen B Λ φ j')
    (fcPull B Λ φ a) (fcPull B Λ φ g)
    (fcPull B Λ φ j) (fcPull B Λ φ j')
    (upperStarCompIso (ModuleCat.{u + 1} Λ) w).hom
    (moduleSquareG B a j' j g w).inv
    (fcOpen_mate B Λ φ j) (fcOpen_mate B Λ φ j')
    (by
      simpa only [openImmersionLowerShriekBaseChangeIso, asIso_hom] using!
        mateEquiv_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq)
    (by
      change mateEquiv (moduleJAdj B j) (moduleJAdj B j')
        (singleBetaInv B a j' j g w) = _
      exact moduleInv_mate B a j' j g w)
    (fun N ↦ fcPull_square B Λ φ a j' j g w N) M

attribute [local irreducible] scalarPaste scalarAlphaPaste ScalarCompatible
  Functor.leftAdjoint

private lemma fcPull_comp (V W Z : Scheme.{u}) (f : V ⟶ W) (g : W ⟶ Z) :
    ScalarCompatible (upperStarComp (ModuleCat.{u + 1} Λ) f g).hom
      (moduleGComp B f g).hom (fcPull B Λ φ (f ≫ g)).symm
      (scalarPaste (fcPull B Λ φ g).symm (fcPull B Λ φ f).symm) := by
  apply scalarCompatible_of_inverse
  intro M
  have hh := congrArg (fun t ↦ t.app M) (fcPull_compSquare B Λ φ f g)
  simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, scalarPaste_inv, Iso.symm_inv,
    Category.assoc] using hh.symm

private lemma fcProject {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] [IsClosedImmersion f]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (C B X Λ φ).map ((cbcClopenProjection Λ f).app M) ≫
      (fcOpen B Λ φ f).inv.app ((upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
      (moduleJ B f).map ((fcPull B Λ φ f).inv.app M) =
    (clopenModulePi B f).app ((C B X Λ φ).obj M) := by
  let O : X.Opens :=
    ⟨(Set.range f)ᶜ, f.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hpΛ := pro_projection_restrict Λ f M
  have hpB := (clopenModule_section_projector B f O.ι
    (Scheme.Opens.range_ι O)).2.1 ((C B X Λ φ).obj M)
  have hu (N : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ)) :
      (C B U Λ φ).map
          ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app N) ≫
        (fcPull B Λ φ f).inv.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) f).obj N) ≫
        (modulePullback B f).map ((fcOpen B Λ φ f).inv.app N) =
      (moduleJAdj B f).unit.app ((C B U Λ φ).obj N) := by
    have hh := unit_mateEquiv
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (moduleJAdj B f) (TwoSquare.mk _ _ _ _ (fcOpen B Λ φ f).hom) N
    rw [fcOpen_mate] at hh
    change _ = _ ≫ (modulePullback B f).map ((fcOpen B Λ φ f).hom.app N) at hh
    rw [← Category.assoc, hh]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id, Functor.id_obj]
  have hn := (fcPull B Λ φ f).inv.naturality ((cbcClopenProjection Λ f).app M)
  dsimp only [Functor.comp_map] at hn
  have he : (modulePullback B f).map
      ((C B X Λ φ).map ((cbcClopenProjection Λ f).app M) ≫
        (fcOpen B Λ φ f).inv.app ((upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
        (moduleJ B f).map ((fcPull B Λ φ f).inv.app M)) =
      (modulePullback B f).map ((clopenModulePi B f).app ((C B X Λ φ).obj M)) := by
    apply (cancel_epi ((fcPull B Λ φ f).inv.app M)).1
    simp only [Functor.map_comp, ← Category.assoc]
    erw [← hn, hpΛ]
    simp only [Category.assoc]
    erw [reassoc_of% hu]
    erw [← (moduleJAdj B f).unit.naturality ((fcPull B Λ φ f).inv.app M), hpB]
    rfl
  have ht := clopenModuleToDirect_isIso B f
  apply (cancel_mono ((clopenModuleToDirect B f).app
    ((modulePullback B f).obj ((C B X Λ φ).obj M)))).1
  apply ((clopenModuleAdj B f).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp]
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun z ↦ z ≫ (modulePullback B f).map
      ((clopenModuleToDirect B f).app
        ((modulePullback B f).obj ((C B X Λ φ).obj M))) ≫
      (clopenModuleAdj B f).counit.app
        ((modulePullback B f).obj ((C B X Λ φ).obj M))) he

omit [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] in
private lemma fcOpenComp_conjugate {U V X : Scheme.{u}}
    (j : U ⟶ V) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k] :
    conjugateEquiv
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k))
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (j ≫ k))
      (proEtaleOpenExtensionComp Λ j k).hom =
        (upperStarComp (ModuleCat.{u + 1} Λ) j k).inv := by
  exact congrArg Iso.hom (CategoryTheory.conj_uniq_transport
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (j ≫ k))
    ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k))
    (upperStarComp (ModuleCat.{u + 1} Λ) j k).symm)

private lemma fcOpen_comp {U V X : Scheme.{u}}
    (j : U ⟶ V) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k] :
    ScalarCompatible (proEtaleOpenExtensionComp Λ j k).inv
      (openBetaModuleJComp B j k).hom
      (scalarPaste (fcOpen B Λ φ j).symm (fcOpen B Λ φ k).symm)
      (fcOpen B Λ φ (j ≫ k)).symm := by
  apply scalarCompatible_inv (e := proEtaleOpenExtensionComp Λ j k)
    (e' := (openBetaModuleJComp B j k).symm)
  let q := (TwoSquare.mk _ _ _ _ (fcOpen B Λ φ j).hom).vComp
    (TwoSquare.mk _ _ _ _ (fcOpen B Λ φ k).hom)
  let r := TwoSquare.mk _ _ _ _ (fcOpen B Λ φ (j ≫ k)).hom
  have hc : q.whiskerRight (openBetaModuleJComp B j k).inv =
      r.whiskerLeft (proEtaleOpenExtensionComp Λ j k).hom := by
    apply (mateEquiv
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k))
      (moduleJAdj B (j ≫ k))).injective
    rw [mateEquiv_conjugateEquiv_vcomp
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k))
      ((moduleJAdj B j).comp (moduleJAdj B k)) (moduleJAdj B (j ≫ k)),
      conjugateEquiv_mateEquiv_vcomp
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k))
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (j ≫ k))
      (moduleJAdj B (j ≫ k))]
    dsimp only [q, r]
    rw [mateEquiv_hcomp, fcOpen_mate, fcOpen_mate, fcOpen_mate]
    rw [scalarJComp_conjugate, fcOpenComp_conjugate]
    refine NatTrans.ext (funext fun M ↦ ?_)
    simpa only [ScalarCompatible, scalarPaste_hom, Iso.symm_hom,
      TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using
      (scalarCompatible_apply (scalarCompatible_inv (e := upperStarComp
        (ModuleCat.{u + 1} Λ) j k) (e' := moduleGComp B j k)
        (fcPull_comp B Λ φ U V X j k)) M).symm
  apply scalarCompatible_of_inverse
  intro M
  have hh := congrArg (fun z ↦ z.app M) hc
  simp only [q, r, TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hh
  simpa only [scalarPaste_inv, Iso.symm_inv, Iso.symm_hom,
    Category.assoc] using hh.symm

private lemma fcOpen_congr {U X : Scheme.{u}}
    {f g : U ⟶ X} [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    ScalarCompatible (u₀ := C B U Λ φ) (u₁ := C B X Λ φ)
      (F := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) f)
      (G := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) g)
      (F' := moduleJ B f) (G' := moduleJ B g)
      (cbcOpenCongr Λ h).hom (singleJCongr B h).hom
      (fcOpen B Λ φ f).symm (fcOpen B Λ φ g).symm := by
  exact scalarCompatible_transport
    (u₀ := C B U Λ φ) (u₁ := C B X Λ φ)
    (fun x : {q : U ⟶ X // IsOpenImmersion q} ↦
      letI := x.property; openImmersionLowerShriek (ModuleCat.{u + 1} Λ) x.val)
    (fun x ↦ letI := x.property; moduleJ B x.val)
    (fun x ↦ letI := x.property; (fcOpen B Λ φ x.val).symm)
    (fun {x y} e ↦ letI := x.property; letI := y.property
      (cbcOpenCongr Λ (congrArg Subtype.val e)).hom)
    (fun {x y} e ↦ letI := x.property; letI := y.property
      (singleJCongr B (congrArg Subtype.val e)).hom)
    (fun x ↦ letI := x.property; rfl)
    (fun x ↦ letI := x.property; singleJCongr_refl B x.val)
    (x := ⟨f, inferInstance⟩) (y := ⟨g, inferInstance⟩) (Subtype.ext h)

private lemma fcPull_congr {U X : Scheme.{u}} {f g : U ⟶ X} (h : f = g) :
    ScalarCompatible (u₀ := C B X Λ φ) (u₁ := C B U Λ φ)
      (F := upperStar (ModuleCat.{u + 1} Λ) f)
      (G := upperStar (ModuleCat.{u + 1} Λ) g)
      (F' := modulePullback B f) (G' := modulePullback B g)
      (cbcPullCongr Λ h).hom (eqToIso (congrArg (modulePullback B) h)).hom
      (fcPull B Λ φ f).symm (fcPull B Λ φ g).symm := by
  subst g
  exact scalarCompatible_identity _

private lemma fcLiftAlpha
    {U V W S T : Scheme.{u}} (q : U ⟶ S) (b : U ⟶ W) (s : V ⟶ U)
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion b]
    [IsOpenImmersion k] [IsOpenImmersion i]
    (hpb : q ≫ i = b ≫ p) (sq : IsPullback q b i p)
    (hb : s ≫ b = k) (hq : s ≫ q = r) :
    ScalarCompatible
      (scalarAlphaPaste (upperStar (ModuleCat.{u + 1} Λ) q)
        (upperStar (ModuleCat.{u + 1} Λ) s)
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b)
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
        (upperStar (ModuleCat.{u + 1} Λ) p)
        (upperStar (ModuleCat.{u + 1} Λ) r)
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
        (cbcClopenProjection Λ s)
        (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sq).inv
        ((proEtaleOpenExtensionComp Λ s b).inv ≫ (cbcOpenCongr Λ hb).hom)
        ((upperStarComp (ModuleCat.{u + 1} Λ) s q).inv ≫ (cbcPullCongr Λ hq).hom))
      (scalarLiftAlpha B q b s k r p i hpb sq hb hq)
      (scalarPaste (fcOpen B Λ φ i).symm (fcPull B Λ φ p).symm)
      (scalarPaste (fcPull B Λ φ r).symm (fcOpen B Λ φ k).symm) := by
  have hj := scalarCompatible_comp
    (fcOpen_comp B Λ φ s b) (fcOpen_congr B Λ φ hb)
  have hg := scalarCompatible_comp
    (scalarCompatible_inv (e := upperStarComp (ModuleCat.{u + 1} Λ) s q)
      (e' := moduleGComp B s q) (fcPull_comp B Λ φ V U S s q))
    (fcPull_congr B Λ φ hq)
  have hβ : ScalarCompatible
      (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sq).inv
      (openBetaModule B q b i p hpb sq).hom
      (scalarPaste (fcOpen B Λ φ i).symm (fcPull B Λ φ p).symm)
      (scalarPaste (fcPull B Λ φ q).symm (fcOpen B Λ φ b).symm) := by
    apply scalarCompatible_of_inverse
    intro M
    simpa only [scalarPaste_inv, Iso.symm_inv, Functor.comp_obj, Category.assoc] using
      (fcOpen_cube B Λ φ q b i p hpb sq M).symm
  exact scalarCompatible_six
    (upperStar (ModuleCat.{u + 1} Λ) q) (modulePullback B q)
    (upperStar (ModuleCat.{u + 1} Λ) s) (modulePullback B s)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s) (moduleJ B s)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b) (moduleJ B b)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) (moduleJ B i)
    (upperStar (ModuleCat.{u + 1} Λ) p) (modulePullback B p)
    (upperStar (ModuleCat.{u + 1} Λ) r) (modulePullback B r)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) (moduleJ B k)
    (fcPull B Λ φ q).symm (fcPull B Λ φ s).symm
    (fcOpen B Λ φ s).symm (fcOpen B Λ φ b).symm
    (fcOpen B Λ φ i).symm (fcPull B Λ φ p).symm
    (fcPull B Λ φ r).symm (fcOpen B Λ φ k).symm
    (cbcClopenProjection Λ s) (clopenModulePi B s)
    (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sq).inv
    (openBetaModule B q b i p hpb sq).hom
    ((proEtaleOpenExtensionComp Λ s b).inv ≫ (cbcOpenCongr Λ hb).hom)
    ((openBetaModuleJComp B s b).hom ≫ (singleJCongr B hb).hom)
    ((upperStarComp (ModuleCat.{u + 1} Λ) s q).inv ≫ (cbcPullCongr Λ hq).hom)
    ((moduleGComp B s q).inv ≫ (eqToIso (congrArg (modulePullback B) hq)).hom)
    (fcProject B Λ φ s) hβ hj hg

private lemma fcAlpha
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} Λ)) :
    (C B W Λ φ).map ((cbcClopenAlphaSheaf Λ k i r p h).app M) ≫
      (fcOpen B Λ φ k).inv.app ((upperStar (ModuleCat.{u + 1} Λ) r).obj M) ≫
      (moduleJ B k).map ((fcPull B Λ φ r).inv.app M) =
    (fcPull B Λ φ p).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M) ≫
      (modulePullback B p).map ((fcOpen B Λ φ i).inv.app M) ≫
      (singleAlpha B k r p i h).app ((C B S Λ φ).obj M) := by
  have ht := fcLiftAlpha B Λ φ (pullback.snd p i) (pullback.fst p i)
    (squareLift k r p i h) k r p i pullback.condition.symm
    (IsPullback.of_hasPullback p i).flip (pullback.lift_fst k r h)
    (pullback.lift_snd k r h)
  have he : scalarAlphaPaste (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i))
      (upperStar (ModuleCat.{u + 1} Λ) (squareLift k r p i h))
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (squareLift k r p i h))
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst p i))
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
      (upperStar (ModuleCat.{u + 1} Λ) p) (upperStar (ModuleCat.{u + 1} Λ) r)
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
      (cbcClopenProjection Λ (squareLift k r p i h))
      (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback p i).flip).inv
      ((proEtaleOpenExtensionComp Λ (squareLift k r p i h) (pullback.fst p i)).inv ≫
        (cbcOpenCongr Λ (pullback.lift_fst k r h)).hom)
      ((upperStarComp (ModuleCat.{u + 1} Λ)
        (squareLift k r p i h) (pullback.snd p i)).inv ≫
        (cbcPullCongr Λ (pullback.lift_snd k r h)).hom) =
        cbcClopenAlphaSheaf Λ k i r p h := by
    simp only [scalarAlphaPaste, cbcClopenAlphaSheaf,
      openImmersionLowerShriekBaseChangeIso, asIso_inv]
  rw [he, scalarLiftAlpha_eq] at ht
  simpa only [scalarPaste_hom, Iso.symm_hom, Category.assoc] using
    scalarCompatible_apply ht M
attribute [local semireducible] upperStar upperStarLowerStarAdjunction modulePullback

private def fcHCompIso
    {A D E F K L : Type*} [Category A] [Category D] [Category E] [Category F]
    [Category K] [Category L]
    {G₁ : A ⥤ E} {G₂ : E ⥤ K} {H₁ : D ⥤ F} {H₂ : F ⥤ L}
    {P₁ : A ⥤ D} {P₂ : E ⥤ F} {P₃ : K ⥤ L}
    (α : G₁ ⋙ P₂ ≅ P₁ ⋙ H₁) (β : G₂ ⋙ P₃ ≅ P₂ ⋙ H₂) :
    (G₁ ⋙ G₂) ⋙ P₃ ≅ P₁ ⋙ H₁ ⋙ H₂ :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G₁ β ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α H₂ ≪≫
    Functor.associator _ _ _

private lemma fcHCompIso_hom
    {A D E F K L : Type*} [Category A] [Category D] [Category E] [Category F]
    [Category K] [Category L]
    {G₁ : A ⥤ E} {G₂ : E ⥤ K} {H₁ : D ⥤ F} {H₂ : F ⥤ L}
    {P₁ : A ⥤ D} {P₂ : E ⥤ F} {P₃ : K ⥤ L}
    (α : G₁ ⋙ P₂ ≅ P₁ ⋙ H₁) (β : G₂ ⋙ P₃ ≅ P₂ ⋙ H₂) :
    (fcHCompIso α β).hom =
      (TwoSquare.hComp (TwoSquare.mk _ _ _ _ α.hom)
        (TwoSquare.mk _ _ _ _ β.hom)) := by
  rfl

private lemma fcHCompIso_inv
    {A D E F K L : Type*} [Category A] [Category D] [Category E] [Category F]
    [Category K] [Category L]
    {G₁ : A ⥤ E} {G₂ : E ⥤ K} {H₁ : D ⥤ F} {H₂ : F ⥤ L}
    {P₁ : A ⥤ D} {P₂ : E ⥤ F} {P₃ : K ⥤ L}
    (α : G₁ ⋙ P₂ ≅ P₁ ⋙ H₁) (β : G₂ ⋙ P₃ ≅ P₂ ⋙ H₂) :
    (fcHCompIso α β).inv =
      (TwoSquare.vComp (TwoSquare.mk _ _ _ _ α.inv)
        (TwoSquare.mk _ _ _ _ β.inv)) := by
  ext M
  simp [fcHCompIso, TwoSquare.vComp]

private lemma fcSitePull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    hPullbackInv B f Λ φ =
      ((TwoSquare.mk _ _ _ _
        (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) f).inv).hComp
        (TwoSquare.mk _ _ _ _ (fcPull B Λ φ f).hom)) := by
  let a := cbcEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f
  let b := cbcProEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f
  let c := Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)
  let α := (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) f).inv
  let β := TwoSquare.mk _ _ _ _ (fcPull B Λ φ f).hom
  have ht := mateEquiv_vcomp a b c α β
  have hm : mateEquiv b c β =
      TwoSquare.mk _ _ _ _ (cDirect B f Λ φ).hom := by
    change mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (openBetaModuleAdj B f) (fcPull B Λ φ f).hom = _
    exact fcPull_mate B Λ φ f
  rw [hm] at ht
  apply (mateEquiv a c).injective
  change (mateEquiv a c) ((mateEquiv a c).symm (hDirect B f Λ φ)) = _
  rw [Equiv.apply_symm_apply]
  exact ht.symm

private lemma fcSitePullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    hPullbackIso B Λ φ f =
      fcHCompIso (cbcComparisonCoefficientPullbackIso
        (ModuleCat.{u + 1} Λ) f).symm (fcPull B Λ φ f) := by
  apply Iso.ext
  rw [fcHCompIso_hom]
  exact fcSitePull B Λ φ f

private lemma fcSitePullInv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (hPullbackIso B Λ φ f).inv.app M =
      (C B X Λ φ).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app M) ≫
      (fcPull B Λ φ f).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj M) := by
  have hs : cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) f =
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm :=
    pullback_comparison_eq Λ f
  rw [fcSitePullIso, fcHCompIso_inv]
  simp only [TwoSquare.vComp, TwoSquare.mk, Iso.symm_inv,
    hs, Iso.symm_hom, cbcComparisonCoefficientPullback, comparisonUpperStar,
    Scheme.smallEtaleTopology]
  rfl

private lemma fcSiteOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (hOpen B j Λ φ).app M =
      (C B X Λ φ).map
        ((openImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} Λ) j).hom.app M) ≫
      (fcOpen B Λ φ j).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj M) := by
  let := hPullbackInv_isIso B j Λ φ
  let := hOpenInv_isIso B j Λ φ
  let oa := Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j
  let ob := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j
  let oc := moduleJAdj B j
  let e := openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j
  have hs : mateEquiv oa ob (TwoSquare.mk _ _ _ _ e.inv) =
      TwoSquare.mk _ _ _ _
        (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j).hom := by
    exact comparison_extension_mate Λ j
  have hi : CategoryTheory.inv (hPullbackInv B j Λ φ) =
      ((TwoSquare.mk _ _ _ _
        (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j).hom).vComp
        (TwoSquare.mk _ _ _ _ (fcPull B Λ φ j).inv)) := by
    change (hPullbackIso B Λ φ j).inv = _
    rw [fcSitePullIso, fcHCompIso_inv]
    rfl
  have ho : hOpenInv B j Λ φ =
      ((TwoSquare.mk _ _ _ _ e.inv).hComp
        (TwoSquare.mk _ _ _ _ (fcOpen B Λ φ j).hom)) := by
    unfold hOpenInv
    rw [hi]
    have hm := mateEquiv_vcomp oa ob oc
      (TwoSquare.mk _ _ _ _ e.inv)
      (TwoSquare.mk _ _ _ _ (fcOpen B Λ φ j).hom)
    rw [hs, fcOpen_mate] at hm
    exact
      ((mateEquiv oa oc).symm_apply_eq.mpr hm.symm)
  have he : @asIso _ _ _ _ (hOpenInv B j Λ φ) (hOpenInv_isIso B j Λ φ) =
      fcHCompIso e.symm (fcOpen B Λ φ j) := by
    apply Iso.ext
    rw [fcHCompIso_hom]
    exact ho
  change (@asIso _ _ _ _ (hOpenInv B j Λ φ) (hOpenInv_isIso B j Λ φ)).inv.app M = _
  rw [he, fcHCompIso_inv]
  simp only [TwoSquare.vComp, TwoSquare.mk,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_inv,
    Category.id_comp, Category.comp_id, e]

private lemma fcMapTriple
    {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {X A B C D' Y : D} (a : X ⟶ A) (b : A ⟶ B) (c : B ⟶ Y)
    (d : X ⟶ C) (e : C ⟶ D') (f : D' ⟶ Y) (h : a ≫ b ≫ c = d ≫ e ≫ f) :
    F.map a ≫ F.map b ≫ F.map c = F.map d ≫ F.map e ≫ F.map f := by
  simpa only [Functor.map_comp] using congrArg F.map h

private lemma fcPasting
    {D E F : Type*} [Category D] [Category E] [Category F]
    (J : D ⥤ F) (P : E ⥤ F) {A₀ A₁ A₂ A₃ A₄ A₅ : F}
    {U₀ U₁ U₂ : D} {V₀ V₁ V₂ : E}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ J.obj U₀)
    (d : U₀ ⟶ U₁) (e : U₁ ⟶ U₂) (u : A₂ ⟶ A₃) (v : A₃ ⟶ J.obj U₁)
    (j : A₀ ⟶ A₄) (k : A₄ ⟶ A₅) (l : A₅ ⟶ A₃)
    (m : A₅ ⟶ P.obj V₁) (n : V₁ ⟶ V₂) (z : P.obj V₂ ⟶ J.obj U₂)
    (p : A₄ ⟶ P.obj V₀) (q : V₀ ⟶ V₁)
    (h₁ : u ≫ v = c ≫ J.map d) (h₂ : a ≫ b ≫ u = j ≫ k ≫ l)
    (h₃ : l ≫ v ≫ J.map e = m ≫ P.map n ≫ z) (h₄ : k ≫ m = p ≫ P.map q) :
    a ≫ (b ≫ c) ≫ J.map (d ≫ e) = (j ≫ p) ≫ P.map (q ≫ n) ≫ z := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h₁, reassoc_of% h₂, h₃, reassoc_of% h₄]

private lemma fcNaturality
    {D E F G : Type*} [Category D] [Category E] [Category F] [Category G]
    (P : D ⥤ E) (Q : E ⥤ G) (R : D ⥤ F) (S : F ⥤ G)
    (t : P ⋙ Q ⟶ R ⋙ S) {X Y : D} (f : X ⟶ Y) :
    Q.map (P.map f) ≫ t.app Y = t.app X ≫ S.map (R.map f) :=
  t.naturality f

attribute [local irreducible] modulePullback upperStar upperStarLowerStarAdjunction
  Etale.upperStar

private lemma fcCombined
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (C B W Λ φ).map
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) W).map
          ((Etale.ClopenMateNormalization.alpha Λ k r p i h).app M)) ≫
      ((C B W Λ φ).map
          ((openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} Λ) k).hom.app
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj M)) ≫
        (fcOpen B Λ φ k).inv.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj M))) ≫
      (moduleJ B k).map
        ((C B V Λ φ).map
            ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) r).inv.app M) ≫
          (fcPull B Λ φ r).inv.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj M)) =
    ((C B W Λ φ).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) p).inv.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M)) ≫
      (fcPull B Λ φ p).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) T).obj
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M))) ≫
      (modulePullback B p).map
        ((C B T Λ φ).map
            ((openImmersionLowerShriekComparisonUpperStarIso
              (ModuleCat.{u + 1} Λ) i).hom.app M) ≫
          (fcOpen B Λ φ i).inv.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj M)) ≫
      (singleAlpha B k r p i h).app
        ((C B S Λ φ).obj ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj M)) := by
  have hn := fcNaturality
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) (C B W Λ φ)
    (C B V Λ φ) (moduleJ B k) (fcOpen B Λ φ k).inv
    ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) r).inv.app M)
  have hs := fcMapTriple (C B W Λ φ)
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) W).map
      ((Etale.ClopenMateNormalization.alpha Λ k r p i h).app M))
    ((openImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ) k).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj M))
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).map
      ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) r).inv.app M))
    ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) p).inv.app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M))
    ((upperStar (ModuleCat.{u + 1} Λ) p).map
      ((openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) i).hom.app M))
    ((cbcClopenAlphaSheaf Λ k i r p h).app
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj M))
    (sheaf_alpha_transport Λ k i r p h M)
  have hp := fcNaturality
    (upperStar (ModuleCat.{u + 1} Λ) p) (C B W Λ φ)
    (C B T Λ φ) (modulePullback B p) (fcPull B Λ φ p).inv
    ((openImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ) i).hom.app M)
  exact fcPasting (moduleJ B k) (modulePullback B p)
    ((C B W Λ φ).map ((comparisonUpperStar (ModuleCat.{u + 1} Λ) W).map
      ((Etale.ClopenMateNormalization.alpha Λ k r p i h).app M)))
    ((C B W Λ φ).map ((openImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ) k).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj M)))
    ((fcOpen B Λ φ k).inv.app ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj M)))
    ((C B V Λ φ).map
      ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) r).inv.app M))
    ((fcPull B Λ φ r).inv.app
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj M))
    ((C B W Λ φ).map ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).map
      ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) r).inv.app M)))
    ((fcOpen B Λ φ k).inv.app ((upperStar (ModuleCat.{u + 1} Λ) r).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj M)))
    ((C B W Λ φ).map
      ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) p).inv.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M)))
    ((C B W Λ φ).map ((upperStar (ModuleCat.{u + 1} Λ) p).map
      ((openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) i).hom.app M)))
    ((C B W Λ φ).map ((cbcClopenAlphaSheaf Λ k i r p h).app
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj M)))
    ((fcPull B Λ φ p).inv.app ((openImmersionLowerShriek
      (ModuleCat.{u + 1} Λ) i).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj M)))
    ((fcOpen B Λ φ i).inv.app
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj M))
    ((singleAlpha B k r p i h).app
      ((C B S Λ φ).obj ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj M)))
    ((fcPull B Λ φ p).inv.app ((comparisonUpperStar (ModuleCat.{u + 1} Λ) T).obj
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M)))
    ((C B T Λ φ).map ((openImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ) i).hom.app M))
    hn hs (fcAlpha B Λ φ k r p i h
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj M)) hp

private def fcHIso (X : Scheme.{u}) :
    H B X Λ φ ≅ comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙ C B X Λ φ :=
  Iso.refl _

attribute [local irreducible] H fcHIso

private lemma fcHIso_naturality {X : Scheme.{u}}
    {M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (a : M ⟶ N) :
    (H B X Λ φ).map a ≫ (fcHIso B Λ φ X).hom.app N =
      (fcHIso B Λ φ X).hom.app M ≫
        (C B X Λ φ).map ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map a) :=
  (fcHIso B Λ φ X).hom.naturality a

attribute [local semireducible] H

private lemma fcHIso_open {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (hOpen B j Λ φ).app M ≫ (moduleJ B j).map ((fcHIso B Λ φ U).hom.app M) =
      (fcHIso B Λ φ X).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj M) ≫
        (C B X Λ φ).map
          ((openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} Λ) j).hom.app M) ≫
        (fcOpen B Λ φ j).inv.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj M) := by
  unfold fcHIso
  exact (congrArg (fun z ↦ (hOpen B j Λ φ).app M ≫ z)
    ((moduleJ B j).map_id _)).trans
      ((Category.comp_id _).trans
        ((fcSiteOpen B Λ φ j M).trans (Category.id_comp _).symm))

private lemma fcHIso_pull {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (hPullbackIso B Λ φ f).inv.app M ≫
        (modulePullback B f).map ((fcHIso B Λ φ Y).hom.app M) =
      (fcHIso B Λ φ X).hom.app ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
        (C B X Λ φ).map
          ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app M) ≫
        (fcPull B Λ φ f).inv.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj M) := by
  unfold fcHIso
  exact (congrArg (fun z ↦ (hPullbackIso B Λ φ f).inv.app M ≫ z)
    ((modulePullback B f).map_id _)).trans
      ((Category.comp_id _).trans
        ((fcSitePullInv B Λ φ f M).trans (Category.id_comp _).symm))

attribute [local irreducible] H

private lemma fcTransport
    {D E F G : Type*} [Category D] [Category E] [Category F] [Category G]
    (J : E ⥤ G) (R : D ⥤ E) (P : F ⥤ G) (I : D ⥤ F)
    (t : I ⋙ P ⟶ R ⋙ J)
    {X X' Y Y' : G} {U U' : E} {Q Q' : F} {S S' : D}
    (a : X ⟶ Y) (b : Y ⟶ J.obj U) (c : U ⟶ R.obj S)
    (d : X ⟶ P.obj Q) (e : Q ⟶ I.obj S)
    (a' : X' ⟶ Y') (b' : Y' ⟶ J.obj U') (c' : U' ⟶ R.obj S')
    (d' : X' ⟶ P.obj Q') (e' : Q' ⟶ I.obj S')
    (sx : X ⟶ X') (sy : Y ⟶ Y') (su : U ⟶ U') (sq : Q ⟶ Q')
    (ss : S ≅ S')
    (ha : a ≫ sy = sx ≫ a') (hb : b ≫ J.map su = sy ≫ b')
    (hc : c ≫ R.map ss.hom = su ≫ c')
    (hd : d ≫ P.map sq = sx ≫ d') (he : e ≫ I.map ss.hom = sq ≫ e')
    (h : a' ≫ b' ≫ J.map c' = d' ≫ P.map e' ≫ t.app S') :
    a ≫ b ≫ J.map c = d ≫ P.map e ≫ t.app S := by
  apply (cancel_mono (J.map (R.map ss.hom))).mp
  have hc' := congrArg J.map hc
  have he' := congrArg P.map he
  simp only [Functor.map_comp] at hc' he'
  have ht : t.app S ≫ J.map (R.map ss.hom) =
      P.map (I.map ss.hom) ≫ t.app S' := (t.naturality ss.hom).symm
  simp only [Category.assoc]
  rw [hc', reassoc_of% hb, reassoc_of% ha,
    ht, reassoc_of% he', reassoc_of% hd, h]

attribute [local irreducible] hOpen hPullbackIso singleAlpha

/-- Coefficient realization preserves the clopen alpha before taking proper mates.
Source: Stacks Project, proetale.tex Tags 099R and 09AF, sites-modules.tex Tag 03DA,
and sites-cohomology.tex Tag 07A7; steps 1--2
of lem-cbc-single-level-finite-proper-open-transport
(blueprint: lem-cbc-finite-coefficient-clopen-alpha).

Proof: factor H as site inverse image followed by C, using the ordinary sheaf
alpha equation already proved in FiniteClopenAlphaSiteTransport. For C over the given
ring map, take the inverse mate of the section-normalized cDirect and then the
inverse open mate. Naturality of cUnderlying and its section equation for cDirect
prove composition of the direct comparisons. Mate pasting gives composition and
commutative-square coherence of the pullback comparisons. The mate-cube identity
then compares the cartesian open base-change maps. For a clopen immersion, the
restriction of the specified projector is the open-adjunction unit. The open mate
unit equation and naturality identify these restrictions after C. Maps into clopen
extension are detected by restriction, using its isomorphism with direct image and
the pullback/direct-image adjunction. Thus the projectors agree as well. Mate
injectivity compares the open compositors; equality transport gives the remaining
congruence maps. Composing these comparisons along the clopen lift gives the
ordinary coefficient alpha equation. Finally mate pasting factors hPullbackInv
and hOpen through the site and coefficient comparisons, and pasting the two alpha
equations proves the assertion. An explicit natural isomorphism from H to its
site-coefficient composite transports the equation without expanding the functors.
This argument works directly for arbitrary B and
phi: it needs no flatness or scalar-factorization hypothesis. Empty clopen images
and complements and zero coefficient rings are covered by the same adjunction
and projector identities. -/
theorem finiteCoefficientClopenAlpha
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (H B W Λ φ).map ((Etale.ClopenMateNormalization.alpha Λ k r p i h).app M) ≫
      (hOpen B k Λ φ).app ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj M) ≫
      (moduleJ B k).map ((hPullbackIso B Λ φ r).inv.app M) =
    (hPullbackIso B Λ φ p).inv.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M) ≫
      (modulePullback B p).map ((hOpen B i Λ φ).app M) ≫
      (singleAlpha B k r p i h).app ((H B S Λ φ).obj M) := by
  exact fcTransport (moduleJ B k) (modulePullback B r)
    (modulePullback B p) (moduleJ B i) (singleAlpha B k r p i h)
    ((H B W Λ φ).map ((Etale.ClopenMateNormalization.alpha Λ k r p i h).app M))
    ((hOpen B k Λ φ).app ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj M))
    ((hPullbackIso B Λ φ r).inv.app M)
    ((hPullbackIso B Λ φ p).inv.app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M))
    ((hOpen B i Λ φ).app M)
    ((C B W Λ φ).map ((comparisonUpperStar (ModuleCat.{u + 1} Λ) W).map
      ((Etale.ClopenMateNormalization.alpha Λ k r p i h).app M)))
    ((C B W Λ φ).map ((openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) k).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj M)) ≫
      (fcOpen B Λ φ k).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj M)))
    ((C B V Λ φ).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) r).inv.app M) ≫
      (fcPull B Λ φ r).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj M))
    ((C B W Λ φ).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) p).inv.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M)) ≫
      (fcPull B Λ φ p).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) T).obj
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M)))
    ((C B T Λ φ).map
        ((openImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} Λ) i).hom.app M) ≫
      (fcOpen B Λ φ i).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj M))
    ((fcHIso B Λ φ W).hom.app
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M)))
    ((fcHIso B Λ φ W).hom.app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj M)))
    ((fcHIso B Λ φ V).hom.app
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj M))
    ((fcHIso B Λ φ T).hom.app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M))
    ((fcHIso B Λ φ S).app M)
    (fcHIso_naturality B Λ φ
      ((Etale.ClopenMateNormalization.alpha Λ k r p i h).app M))
    (fcHIso_open B Λ φ k ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj M))
    (fcHIso_pull B Λ φ r M)
    (fcHIso_pull B Λ φ p
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M))
    (fcHIso_open B Λ φ i M)
    (fcCombined B Λ φ k r p i h M)

end CoefficientAlphaProof
end AlgebraicGeometry.ProEtale.StrictTower
