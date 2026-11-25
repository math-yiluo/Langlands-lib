/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedStrictOpenExchange
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenScalars.FiniteOpenExchangeScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDirectImageSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenStrictReduction
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import all WeilConjectures.AlgebraicGeometry.Open.OpenClosedAdjunctionTransport

/-!
# Fixed finite coordinates for completed-ring open exchange

Source: Stacks 03DI, 03D7, 04J0 and 099N; blueprint finite exchange before Rlim
(blueprint: def-cbc-completed-finite-exchange-coordinates).

The scalar comparisons are mates of the sectionwise specified right comparisons.
The level coordinate change is identity on sections. Thus no unrelated finite
coordinate isomorphism is selected.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)

open AlgebraicGeometry.ProEtale.StrictTower

/-- The positive finite quotient, bundled once to avoid repeated ring elaboration.
Source: the coefficient datum (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteRing (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (A ⧸ d.ideal ^ (n + 1))

/-- The bundled finite ring is finite by the coefficient datum.
Source: the coefficient datum (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: this is exactly d.quotientFinite at the positive exponent n+1. -/
@[instance] theorem cbcFiniteRing_finite (n : ℕ) : Finite (cbcFiniteRing d n) := by
  exact d.quotientFinite n

/-- The completed-ring action on constant finite coefficients is the projection
followed by the inverse of the fixed constant-section comparison.
Source: Stacks 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteProjection (T : Scheme.{u}) (n : ℕ) :
    pbcAdicCompletion T d ⟶ coefficients (cbcFiniteRing d n) T :=
  pbcAdicProjection T d n ≫ (pbcLevelConstantComparison T d n).inv

/-- Finite modules with their actual completed-ring scalar action.
Source: Stacks 03CY (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteRes (T : Scheme.{u}) (n : ℕ) := pbcRestrict (cbcFiniteProjection d T n)

private theorem inverseMate_isIso_change_left
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (b' : L₂' ⊣ R₂)
    (α : TwoSquare R₁ H G R₂)
    (hα : IsIso ((mateEquiv a b).symm α)) :
    IsIso ((mateEquiv a b').symm α) := by
  let w := (mateEquiv a b').symm α
  have h := mateEquiv_leftAdjointUniq a a b b' w
  have hself : a.leftAdjointUniq a = Iso.refl _ :=
    Iso.ext (Adjunction.leftAdjointUniq_refl a)
  rw [hself] at h
  simp only [Iso.refl_inv, Functor.whiskerRight_id', Category.comp_id,
    w, Equiv.apply_symm_apply] at h
  have h' := ((mateEquiv a b).injective
    (h.trans (Equiv.apply_symm_apply (mateEquiv a b) α).symm))
  change Functor.whiskerLeft G (b.leftAdjointUniq b').hom ≫ w =
    ((mateEquiv a b).symm α) at h'
  have : IsIso (Functor.whiskerLeft G (b.leftAdjointUniq b').hom ≫ w) := by
    rw [h']
    exact hα
  exact (isIso_comp_left_iff
    (Functor.whiskerLeft G (b.leftAdjointUniq b').hom) w).mp inferInstance

private theorem finiteProjection_pullback {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    completedCoefficientMap f d ≫ cbcFiniteProjection d S n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (cbcFiniteProjection d T n) ≫ (constantRingIso (cbcFiniteRing d n) f).hom := by
  unfold cbcFiniteProjection
  rw [← Category.assoc]
  have h : completedCoefficientMap f d ≫ pbcAdicProjection S d n =
      completedCoefficientComponent f d n := limit.lift_π _ (op n)
  rw [h]
  simp only [completedCoefficientComponent, completedFiniteCoefficientMap,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

private theorem finiteProjection_direct {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    cbcFiniteProjection d T n ≫ proEtaleRingDirectImageMap f
        (coefficients (cbcFiniteRing d n) T) (coefficients (cbcFiniteRing d n) S)
        (constantRingIso (cbcFiniteRing d n) f) =
      cbcCompletedCoefficientDirectMap d f ≫
        (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          (cbcFiniteProjection d S n) := by
  simp only [cbcCompletedCoefficientDirectMap, proEtaleRingDirectImageMap,
    Adjunction.homEquiv_unit]
  have hn := (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.naturality
    (cbcFiniteProjection d T n)
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← Functor.map_comp, ← finiteProjection_pullback d f n,
    Functor.map_comp, Category.assoc]
  rfl

/-- Direct-image coefficient restriction is the identity on underlying sections.
This normalization fixes its mate, rather than choosing a pullback isomorphism.
Source: Stacks 03D7 (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: both direct images evaluate on the same base-changed site object. Their
scalar actions agree after the completed finite projection. Identity on sections
is thus linear, natural, and invertible, and it determines the comparison uniquely. -/
theorem cbcFiniteDirectRes_existsUnique {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    ∃! e : moduleDirectImage (cbcFiniteRing d n) f ⋙ cbcFiniteRes d T n ≅
        cbcFiniteRes d S n ⋙ cbcCompletedModuleDirectImage d f,
      ∀ (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) S) (V : T.ProEtᵒᵖ)
        (x : M.val.obj ((proEtaleBaseChange f).op.obj V)),
        (e.hom.app M).val.app V x = x := by
  let h := finiteProjection_direct d f n
  let eM (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) S) :
      ((moduleDirectImage (cbcFiniteRing d n) f ⋙ cbcFiniteRes d T n).obj M) ≅
        ((cbcFiniteRes d S n ⋙ cbcCompletedModuleDirectImage d f).obj M) :=
    { hom :=
        { val :=
            { app V := ModuleCat.ofHom
                (X := (((moduleDirectImage (cbcFiniteRing d n) f ⋙
                  cbcFiniteRes d T n).obj M).val.obj V))
                (Y := (((cbcFiniteRes d S n ⋙
                  cbcCompletedModuleDirectImage d f).obj M).val.obj V))
                { toFun := id
                  map_add' := fun _ _ ↦ rfl
                  map_smul' := by
                    intro r x
                    change (proEtaleRingDirectImageMap f _ _
                        (constantRingIso (cbcFiniteRing d n) f)).hom.app V
                        ((cbcFiniteProjection d T n).hom.app V r) •
                        (show M.val.obj ((proEtaleBaseChange f).op.obj V) from x) =
                      (cbcFiniteProjection d S n).hom.app
                        ((proEtaleBaseChange f).op.obj V)
                        ((cbcCompletedCoefficientDirectMap d f).hom.app V r) •
                        (show M.val.obj ((proEtaleBaseChange f).op.obj V) from x)
                    congr 1
                    exact congrArg (fun k ↦ k.hom.app V r) h }
              naturality := by intros; ext x; rfl } }
      inv :=
        { val :=
            { app V := ModuleCat.ofHom
                (X := (((cbcFiniteRes d S n ⋙
                  cbcCompletedModuleDirectImage d f).obj M).val.obj V))
                (Y := (((moduleDirectImage (cbcFiniteRing d n) f ⋙
                  cbcFiniteRes d T n).obj M).val.obj V))
                { toFun := id
                  map_add' := fun _ _ ↦ rfl
                  map_smul' := by
                    intro r x
                    change (cbcFiniteProjection d S n).hom.app
                        ((proEtaleBaseChange f).op.obj V)
                        ((cbcCompletedCoefficientDirectMap d f).hom.app V r) •
                        (show M.val.obj ((proEtaleBaseChange f).op.obj V) from x) =
                      (proEtaleRingDirectImageMap f _ _
                        (constantRingIso (cbcFiniteRing d n) f)).hom.app V
                        ((cbcFiniteProjection d T n).hom.app V r) •
                        (show M.val.obj ((proEtaleBaseChange f).op.obj V) from x)
                    congr 1
                    exact congrArg (fun k ↦ k.hom.app V r) h.symm }
              naturality := by intros; ext x; rfl } }
      hom_inv_id := by ext V x; rfl
      inv_hom_id := by ext V x; rfl }
  let e : moduleDirectImage (cbcFiniteRing d n) f ⋙ cbcFiniteRes d T n ≅
      cbcFiniteRes d S n ⋙ cbcCompletedModuleDirectImage d f :=
    NatIso.ofComponents eM (fun k ↦ by ext V x; rfl)
  refine ⟨e, fun _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  ext M V x
  exact he' M V x

/-- The sectionwise direct-image comparison, with its fixed identity normalization.
Source: Stacks 03D7 (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
@[irreducible] def cbcFiniteDirectRes {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :=
  (cbcFiniteDirectRes_existsUnique d f n).exists.choose

/-- The finite pullback comparison is the mate of identity on direct-image sections.
Source: Stacks 03D7 (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFinitePullRes {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    cbcFiniteRes d T n ⋙ completedModulePullback f d ⟶
      modulePullback (cbcFiniteRing d n) f ⋙ cbcFiniteRes d S n :=
  ((mateEquiv
    (proEtaleRingModuleAdjunction f _ _ (constantRingIso (cbcFiniteRing d n) f))
    (cbcModulePullbackAdjunction d f)).symm
      (TwoSquare.mk _ _ _ _ (cbcFiniteDirectRes d f n).hom))

/-- The ordinary pullback mate is invertible at finite coefficients.
Source: Stacks 03EK, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: on inverse-image tensor generators the mate sends b tensor m to pi_n(b)
tensor m. The inverse inserts 1 in the completed tensor factor. The finite
constant-ring comparison and balancing make these maps mutually inverse. -/
@[instance] theorem cbcFinitePullRes_isIso {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    IsIso (cbcFinitePullRes d f n) := by
  have hc : IsIso (completedCoefficientMap f d) := completedCoefficient_isIso f d
  let c := asIso (completedCoefficientMap f d)
  let R := pbcAdicCompletion T d
  let RS := pbcAdicCompletion S d
  let B := coefficients (cbcFiniteRing d n) T
  let B' := coefficients (cbcFiniteRing d n) S
  let cB := constantRingIso (cbcFiniteRing d n) f
  have h : c.hom ≫ cbcFiniteProjection d S n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (cbcFiniteProjection d T n) ≫ cB.hom := finiteProjection_pullback d f n
  let z := proEtaleRingRestrictionDirectImage f R B RS B'
    (cbcFiniteProjection d T n) (cbcFiniteProjection d S n) c cB h
  have hz : z = cbcFiniteDirectRes d f n := by
    apply (cbcFiniteDirectRes_existsUnique d f n).unique
    · exact (proEtaleRingRestrictionDirectImage_existsUnique
        f R B RS B' (cbcFiniteProjection d T n) (cbcFiniteProjection d S n) c cB h)
          |>.choose_spec.1
    · simpa only [cbcFiniteDirectRes] using
        (cbcFiniteDirectRes_existsUnique d f n).exists.choose_spec
  let a := proEtaleRingModuleAdjunction f B B' cB
  let b := proEtaleRingModuleAdjunction f R RS c
  let β := proEtaleRingRestrictionPullbackInv f R B RS B'
    (cbcFiniteProjection d T n) (cbcFiniteProjection d S n) c cB h
  have hβ : IsIso β := proEtaleRingRestrictionPullbackInv_isIso
    f R B RS B' (cbcFiniteProjection d T n) (cbcFiniteProjection d S n) c cB h
  have hm : (mateEquiv a b (TwoSquare.mk _ _ _ _ β)) = z.hom :=
    restrictionPullback_mate f R B RS B'
      (cbcFiniteProjection d T n) (cbcFiniteProjection d S n) c cB h
  have hm' : mateEquiv a b (TwoSquare.mk _ _ _ _ β) =
      TwoSquare.mk _ _ _ _ z.hom := hm
  have hi : IsIso ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ z.hom)) := by
    rw [← hm', Equiv.symm_apply_apply]
    exact hβ
  have hi' := inverseMate_isIso_change_left a b (cbcModulePullbackAdjunction d f)
    (TwoSquare.mk _ _ _ _ z.hom) hi
  rw [hz] at hi'
  exact hi'

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction

private def finiteOpenRing {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    coefficients (cbcFiniteRing d n) W ≅
      ((cbcOpenSiteFunctor e he).sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology W) (ProEt.topology T)).obj (coefficients (cbcFiniteRing d n) T) := by
  have : (cbcOpenSiteFunctor e he).IsCocontinuous
      (ProEt.topology W) (ProEt.topology T) :=
    ProEt.isCocontinuous_overMap (cbcOpenWeaklyEtale e he)
  exact ((cbcOpenSiteFunctor e he).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{u + 1} (ProEt.topology W) (ProEt.topology T)).app
      ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))

private theorem finiteOpenRing_unit {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (cbcFiniteRing d n)) ≫
      (finiteOpenRing d e he n).hom.hom =
    Functor.whiskerLeft (cbcOpenSiteFunctor e he).op
      (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))) := by
  have : (cbcOpenSiteFunctor e he).IsCocontinuous
      (ProEt.topology W) (ProEt.topology T) :=
    ProEt.isCocontinuous_overMap (cbcOpenWeaklyEtale e he)
  exact (cbcOpenSiteFunctor e he).toSheafify_pullbackSheafificationCompatibility
    CommRingCat.{u + 1} (ProEt.topology W) (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))

attribute [local irreducible] finiteOpenRing

private theorem finiteOpenRing_projection {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    cbcFiniteProjection d W n ≫ (finiteOpenRing d e he n).hom =
      cbcCompletedRestrictionMap d e he ≫
        ((cbcOpenSiteFunctor e he).sheafPushforwardContinuous CommRingCat.{u + 1}
          (ProEt.topology W) (ProEt.topology T)).map (cbcFiniteProjection d T n) := by
  let G := (cbcOpenSiteFunctor e he).sheafPushforwardContinuous CommRingCat.{u + 1}
    (ProEt.topology W) (ProEt.topology T)
  have hfin : (pbcLevelConstantComparison W d n).hom ≫
        cbcFiniteRestrictionMap d e he n =
      (finiteOpenRing d e he n).hom ≫ G.map (pbcLevelConstantComparison T d n).hom := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _
      (G.obj (reductionCoefficient T d n)).property
    ext V b
    change (cbcFiniteRestrictionMap d e he n).hom.app V
        ((pbcLevelConstantComparison W d n).hom.hom.app V
          ((toSheafify (ProEt.topology W)
            ((Functor.const W.ProEtᵒᵖ).obj (cbcFiniteRing d n))).app V b)) =
      (pbcLevelConstantComparison T d n).hom.hom.app
        ((cbcOpenSiteFunctor e he).op.obj V)
        ((finiteOpenRing d e he n).hom.hom.app V
          ((toSheafify (ProEt.topology W)
            ((Functor.const W.ProEtᵒᵖ).obj (cbcFiniteRing d n))).app V b))
    erw [(pbcLevelConstantComparison_exists W d n).exists.choose_spec V b]
    have hc := ConcreteCategory.congr_hom (congr_app (finiteOpenRing_unit d e he n) V) b
    change (finiteOpenRing d e he n).hom.hom.app V
        ((toSheafify (ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj (cbcFiniteRing d n))).app V b) = _ at hc
    erw [hc, (pbcLevelConstantComparison_exists T d n).exists.choose_spec]
    exact ConcreteCategory.congr_hom
      ((cbcFiniteRestrictionMap_exists d e he n).exists.choose_spec V)
      (pbcQuotientConstant W d n V b ⊥)
  have hcomp := (cbcCompletedRestrictionMap_exists d e he).exists.choose_spec n
  change cbcCompletedRestrictionMap d e he ≫
      G.map (pbcAdicProjection T d n) =
    pbcAdicProjection W d n ≫ cbcFiniteRestrictionMap d e he n at hcomp
  unfold cbcFiniteProjection
  apply (cancel_mono (G.map (pbcLevelConstantComparison T d n).hom)).mp
  change (pbcAdicProjection W d n ≫ (pbcLevelConstantComparison W d n).inv ≫
      (finiteOpenRing d e he n).hom) ≫ G.map (pbcLevelConstantComparison T d n).hom =
    (cbcCompletedRestrictionMap d e he ≫ G.map
      (pbcAdicProjection T d n ≫ (pbcLevelConstantComparison T d n).inv)) ≫
        G.map (pbcLevelConstantComparison T d n).hom
  rw [G.map_comp]
  simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id, Category.comp_id]
  rw [hcomp]
  erw [← hfin]
  change pbcAdicProjection W d n ≫
      ((pbcLevelConstantComparison W d n).inv ≫
        (pbcLevelConstantComparison W d n).hom ≫ cbcFiniteRestrictionMap d e he n) = _
  rw [Iso.inv_hom_id_assoc]

private def finiteOpenAdjunction {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    SheafOfModules.pushforward.{u + 1} (F := cbcOpenSiteFunctor e he)
      (J := ProEt.topology W) (K := ProEt.topology T)
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (finiteOpenRing d e he n).hom) ⊣ moduleDirectImage (cbcFiniteRing d n) e := by
  let F := proEtaleBaseChange e
  let G := cbcOpenSiteFunctor e he
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
    (cbcOpenWeaklyEtale e he) trivial
  let R := coefficients (cbcFiniteRing d n) T
  let S := coefficients (cbcFiniteRing d n) W
  let c := finiteOpenRing d e he n
  let ψ := proEtaleRingDirectImageMap e R S (constantRingIso (cbcFiniteRing d n) e)
  have hψ : ψ = proEtaleConstantDirectImageMap e CommRingCat.{u + 1}
      (cbcFiniteRing d n) := by
    change (proEtaleSheafAdjunction e CommRingCat.{u + 1}).homEquiv _ _
      (((proEtaleSheafAdjunction e CommRingCat.{u + 1}).homEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      ψ.hom ≫ F.op.whiskerLeft c.hom.hom := by
    apply sheafify_hom_ext (ProEt.topology T) _ _
      (((proEtaleSheafDirectImage e CommRingCat.{u + 1}).obj
        ((G.sheafPushforwardContinuous CommRingCat.{u + 1}
          (ProEt.topology W) (ProEt.topology T)).obj R)).property)
    rw [hψ]
    have hψunit : toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n)) ≫
        (proEtaleConstantDirectImageMap e CommRingCat.{u + 1}
          (cbcFiniteRing d n)).hom =
      F.op.whiskerLeft (toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (cbcFiniteRing d n))) := by
      exact (sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv
        _ _ |>.apply_symm_apply _
    rw [← Category.assoc]
    erw [hψunit]
    ext V b
    have hc := ConcreteCategory.congr_hom
      (congr_app (finiteOpenRing_unit d e he n) (F.op.obj V)) b
    have hn := ConcreteCategory.congr_hom
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))).naturality
          (a.counit.app V.unop).op) b
    exact hn.symm.trans hc.symm
  have H₂ : c.hom.hom ≫ G.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext V
    apply (cancel_mono (c.hom.hom.app V)).mp
    dsimp
    rw [Category.id_comp]
    have hn := c.hom.hom.naturality (a.unit.app V.unop).op
    dsimp at hn
    rw [Category.assoc, Category.assoc, hn]
    have hh := congrArg (fun t ↦ t.app (G.op.obj V)) H₁
    dsimp at hh
    erw [← Category.assoc (ψ.hom.app (G.op.obj V))
      (c.hom.hom.app (F.op.obj (G.op.obj V)))
      (R.obj.map (G.map (a.unit.app V.unop)).op), ← hh]
    rw [← Functor.map_comp, ← op_comp]
    erw [a.left_triangle_components]
    change c.hom.hom.app V ≫ R.obj.map (𝟙 (G.op.obj V)) = c.hom.hom.app V
    rw [R.obj.map_id]
    exact Category.comp_id _
  let Rr := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let Sr := (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let φr : Sr ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology W) (ProEt.topology T)).obj Rr :=
    (sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom
  let ψr : Rr ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology T) (ProEt.topology W)).obj Sr :=
    ⟨Functor.whiskerRight ψ.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have H₁r : Functor.whiskerRight (NatTrans.op a.counit) Rr.obj =
      ψr.hom ≫ F.op.whiskerLeft φr.hom := by
    apply NatTrans.ext
    funext V
    exact congrArg (fun z ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map (z.app V)) H₁
  have H₂r : φr.hom ≫ G.op.whiskerLeft ψr.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) Sr.obj = 𝟙 Sr.obj := by
    apply NatTrans.ext
    funext V
    exact congrArg (fun z ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map (z.app V)) H₂
  change SheafOfModules.pushforward.{u + 1} (F := G) φr ⊣
    SheafOfModules.pushforward.{u + 1} (F := F) ψr
  exact SheafOfModules.pushforwardPushforwardAdj (F := G) (G := F) a φr ψr H₁r H₂r

private theorem finiteOpenAdjunction_unit {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ)
    (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) T)
    (Z : T.ProEt) (m : M.val.obj (op Z)) :
    ((finiteOpenAdjunction d e he n).unit.app M).val.app (op Z) m =
      M.val.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
        (cbcOpenWeaklyEtale e he) trivial).counit.app Z).op m := by
  unfold finiteOpenAdjunction
  rfl

attribute [local irreducible] finiteOpenAdjunction

private def finiteOpenModel {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :=
  (proEtaleRingModuleAdjunction e _ _ (constantRingIso (cbcFiniteRing d n) e)).leftAdjointUniq
    (finiteOpenAdjunction d e he n)

private theorem finiteOpenModel_generator {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ)
    (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) T) (V : W.ProEt) (Z : T.ProEt)
    (f : V ⟶ (proEtaleBaseChange e).obj Z) (m : M.val.obj (op Z)) :
    ((finiteOpenModel d e he n).hom.app M).val.app (op V)
      (((modulePullback (cbcFiniteRing d n) e).obj M).val.map f.op
        (((proEtaleRingModuleAdjunction e _ _
          (constantRingIso (cbcFiniteRing d n) e)).unit.app M).val.app (op Z) m)) =
      M.val.map
        (((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
          (cbcOpenWeaklyEtale e he) trivial).homEquiv V Z).symm f).op m := by
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
    (cbcOpenWeaklyEtale e he) trivial
  let b := proEtaleRingModuleAdjunction e _ _ (constantRingIso (cbcFiniteRing d n) e)
  have hunit := b.unit_leftAdjointUniq_hom_app (finiteOpenAdjunction d e he n) M
  have hn := ((finiteOpenModel d e he n).hom.app M).val.naturality f.op
  have hx := congrArg (fun z ↦ z.hom ((b.unit.app M).val.app (op Z) m)) hn
  have hu : ((finiteOpenModel d e he n).hom.app M).val.app
        (op ((proEtaleBaseChange e).obj Z)) ((b.unit.app M).val.app (op Z) m) =
      M.val.map (a.counit.app Z).op m := by
    rw [← finiteOpenAdjunction_unit d e he n M Z m]
    exact congrArg (fun z ↦ z.val.app (op Z) m) hunit
  change _ = M.val.map ((cbcOpenSiteFunctor e he).map f).op
    (((finiteOpenModel d e he n).hom.app M).val.app
      (op ((proEtaleBaseChange e).obj Z)) ((b.unit.app M).val.app (op Z) m)) at hx
  rw [hu] at hx
  have hc := M.val.map_comp_apply (a.counit.app Z).op
    ((cbcOpenSiteFunctor e he).map f).op m
  exact hx.trans (hc.symm.trans (by rfl))

/-- Open restriction commutes with finite scalar restriction, normalized on the
inverse-image unit generators. The site adjunction supplies the actual restricted
section, so no unidentified comparison of underlying abelian sheaves is used.
Source: Stacks 03DI, 04J0 (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: localization evaluates a sheaf on the same object over the open. On a
base-change generator its value is restriction along the adjoint site arrow.
The coefficient projections identify scalar actions. These formulas give inverse
linear maps after sheafification; the generators determine them uniquely. -/
theorem cbcFiniteOpenRestriction_existsUnique {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    ∃! q : modulePullback (cbcFiniteRing d n) e ⋙ cbcFiniteRes d W n ≅
        cbcFiniteRes d T n ⋙ cbcOpenRestriction d e he,
      ∀ (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) T) (V : W.ProEt) (Z : T.ProEt)
        (f : V ⟶ (proEtaleBaseChange e).obj Z) (m : M.val.obj (op Z)),
        (q.hom.app M).val.app (op V)
          (((modulePullback (cbcFiniteRing d n) e).obj M).val.map f.op
            (((proEtaleRingModuleAdjunction e _ _
              (constantRingIso (cbcFiniteRing d n) e)).unit.app M).val.app (op Z) m)) =
          M.val.map
            (((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
              (cbcOpenWeaklyEtale e he) trivial).homEquiv V Z).symm f).op m := by
  let E := finiteOpenModel d e he n
  have hφ := finiteOpenRing_projection d e he n
  have hs (V : W.ProEtᵒᵖ) (r : (pbcAdicCompletion W d).obj.obj V) :
      (finiteOpenRing d e he n).hom.hom.app V ((cbcFiniteProjection d W n).hom.app V r) =
        (cbcFiniteProjection d T n).hom.app ((cbcOpenSiteFunctor e he).op.obj V)
          ((cbcCompletedRestrictionMap d e he).hom.app V r) :=
    congrArg (fun z ↦ z.hom.app V r) hφ
  let qM (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) T) :
      ((modulePullback (cbcFiniteRing d n) e ⋙ cbcFiniteRes d W n).obj M) ≅
        ((cbcFiniteRes d T n ⋙ cbcOpenRestriction d e he).obj M) :=
    { hom :=
        { val :=
            { app V := ModuleCat.ofHom
                (X := (((modulePullback (cbcFiniteRing d n) e ⋙
                  cbcFiniteRes d W n).obj M).val.obj V))
                (Y := (((cbcFiniteRes d T n ⋙
                  cbcOpenRestriction d e he).obj M).val.obj V))
                { toFun := (E.hom.app M).val.app V
                  map_add' := map_add ((E.hom.app M).val.app V).hom
                  map_smul' := by
                    intro r x
                    change (E.hom.app M).val.app V
                        ((cbcFiniteProjection d W n).hom.app V r •
                          (show ((modulePullback (cbcFiniteRing d n) e).obj M).val.obj V
                            from x)) = _
                    rw [map_smul]
                    change (finiteOpenRing d e he n).hom.hom.app V
                        ((cbcFiniteProjection d W n).hom.app V r) •
                        (show M.val.obj ((cbcOpenSiteFunctor e he).op.obj V)
                          from (E.hom.app M).val.app V x) = _
                    rw [hs]
                    rfl }
              naturality := by
                intro V V' f
                ext x
                exact congrArg (fun z ↦ z.hom x) ((E.hom.app M).val.naturality f) } }
      inv :=
        { val :=
            { app V := ModuleCat.ofHom
                (X := (((cbcFiniteRes d T n ⋙
                  cbcOpenRestriction d e he).obj M).val.obj V))
                (Y := (((modulePullback (cbcFiniteRing d n) e ⋙
                  cbcFiniteRes d W n).obj M).val.obj V))
                { toFun := (E.inv.app M).val.app V
                  map_add' := map_add ((E.inv.app M).val.app V).hom
                  map_smul' := by
                    intro r x
                    change (E.inv.app M).val.app V
                        ((cbcFiniteProjection d T n).hom.app
                          ((cbcOpenSiteFunctor e he).op.obj V)
                          ((cbcCompletedRestrictionMap d e he).hom.app V r) •
                          (show M.val.obj ((cbcOpenSiteFunctor e he).op.obj V) from x)) = _
                    rw [← hs V r]
                    exact map_smul ((E.inv.app M).val.app V).hom
                      ((cbcFiniteProjection d W n).hom.app V r)
                      (show ((SheafOfModules.pushforward.{u + 1}
                        (F := cbcOpenSiteFunctor e he)
                        ((sheafCompose (ProEt.topology W)
                          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                          (finiteOpenRing d e he n).hom)).obj M).val.obj V from x) }
              naturality := by
                intro V V' f
                ext x
                exact congrArg (fun z ↦ z.hom x) ((E.inv.app M).val.naturality f) } }
      hom_inv_id := by
        ext V x
        exact congrArg (fun z ↦ z.val.app V x) (E.hom_inv_id_app M)
      inv_hom_id := by
        ext V x
        exact congrArg (fun z ↦ z.val.app V x) (E.inv_hom_id_app M) }
  let q := NatIso.ofComponents qM (fun f ↦ by
    ext V x
    exact congrArg (fun z ↦ z.val.app V x) (E.hom.naturality f))
  have hq : ∀ (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) T)
      (V : W.ProEt) (Z : T.ProEt) (f : V ⟶ (proEtaleBaseChange e).obj Z)
      (m : M.val.obj (op Z)),
      (q.hom.app M).val.app (op V)
        (((modulePullback (cbcFiniteRing d n) e).obj M).val.map f.op
          (((proEtaleRingModuleAdjunction e _ _
            (constantRingIso (cbcFiniteRing d n) e)).unit.app M).val.app (op Z) m)) =
        M.val.map (((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
          (cbcOpenWeaklyEtale e he) trivial).homEquiv V Z).symm f).op m :=
    finiteOpenModel_generator d e he n
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Iso.ext
  ext M V x
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
    (cbcOpenWeaklyEtale e he) trivial
  let m := (q.hom.app M).val.app V x
  let z := (((modulePullback (cbcFiniteRing d n) e).obj M).val.map
    (a.unit.app V.unop).op
      (((proEtaleRingModuleAdjunction e _ _
        (constantRingIso (cbcFiniteRing d n) e)).unit.app M).val.app
          (op ((cbcOpenSiteFunctor e he).obj V.unop)) m))
  have hz : z = x := by
    apply (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation _ V).map (q.hom.app M))).injective
    have h := hq M V.unop ((cbcOpenSiteFunctor e he).obj V.unop)
      (a.unit.app V.unop) m
    have hid : (a.homEquiv V.unop ((cbcOpenSiteFunctor e he).obj V.unop)).symm
        (a.unit.app V.unop) = 𝟙 _ := a.homEquiv_symm_unit _
    change (q.hom.app M).val.app V z = (q.hom.app M).val.app V x
    change (q.hom.app M).val.app V z = M.val.map
      ((a.homEquiv V.unop ((cbcOpenSiteFunctor e he).obj V.unop)).symm
        (a.unit.app V.unop)).op m at h
    rw [hid] at h
    have hm : M.val.map (𝟙 _).op m = m := by
      have hh := congrArg (fun k ↦ k.hom m) (M.val.map_id _)
      exact hh
    exact h.trans hm
  rw [← hz]
  exact (hq' M V.unop _ (a.unit.app V.unop) m).trans
    (hq M V.unop _ (a.unit.app V.unop) m).symm

/-- The uniquely normalized finite open-restriction comparison.
Source: Stacks 03DI (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
@[irreducible] def cbcFiniteOpenRestriction {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :=
  (cbcFiniteOpenRestriction_existsUnique d e he n).exists.choose

/-- Open extension commutes with the completed action through the finite projection.
This is the mate of the specified open-restriction comparison.
Source: Stacks 03DI (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteOpenRes {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    cbcFiniteRes d W n ⋙ cbcOpenShriek d e he ⟶
      (@moduleJ.{u} (cbcFiniteRing d n) _ W T e he) ⋙ cbcFiniteRes d T n :=
  ((mateEquiv (@moduleJAdj.{u} (cbcFiniteRing d n) _ W T e he)
    (cbcOpenAdjunction d e he)).symm
      (TwoSquare.mk _ _ _ _ (cbcFiniteOpenRestriction d e he n).hom))

private def finiteSliceRing (T : Scheme.{u}) (W : T.ProEt) (n : ℕ) :
    (coefficients (cbcFiniteRing d n) T).over W ≅
      cbcSliceRing W (coefficients (cbcFiniteRing d n) W.left) :=
  ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).mapIso
      (pbcLevelConstantComparison T d n) ≪≫
    cbcFiniteRestriction W d n ≪≫
    ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
      ((ProEt.topology T).over W) (ProEt.topology W.left)).mapIso
        (pbcLevelConstantComparison W.left d n).symm

private theorem finiteSliceRing_unit (T : Scheme.{u}) (W : T.ProEt) (n : ℕ)
    (V : Over W) (b : cbcFiniteRing d n) :
    (finiteSliceRing d T W n).hom.hom.app (op V)
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))).app (op V.left) b) =
    (toSheafify (ProEt.topology W.left)
      ((Functor.const W.left.ProEtᵒᵖ).obj (cbcFiniteRing d n))).app
        (op ((cbcSliceFunctor T W).obj V)) b := by
  apply (ConcreteCategory.bijective_of_isIso
    ((pbcLevelConstantComparison W.left d n).hom.hom.app
      (op ((cbcSliceFunctor T W).obj V)))).injective
  change (pbcLevelConstantComparison W.left d n).hom.hom.app _
    ((pbcLevelConstantComparison W.left d n).inv.hom.app _
      ((cbcFiniteSliceMap d T W n).hom.app (op V)
        ((pbcLevelConstantComparison T d n).hom.hom.app (op V.left)
          ((toSheafify (ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))).app (op V.left) b)))) = _
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app
      (op ((cbcSliceFunctor T W).obj V))) (pbcLevelConstantComparison W.left d n).inv_hom_id)
    ((cbcFiniteSliceMap d T W n).hom.app (op V)
      ((pbcLevelConstantComparison T d n).hom.hom.app (op V.left)
        ((toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))).app (op V.left) b)))
  change (pbcLevelConstantComparison W.left d n).hom.hom.app _
    ((pbcLevelConstantComparison W.left d n).inv.hom.app _ _) = _ at hi
  erw [hi]
  erw [(pbcLevelConstantComparison_exists T d n).exists.choose_spec,
    (pbcLevelConstantComparison_exists W.left d n).exists.choose_spec]
  exact ConcreteCategory.congr_hom
    ((cbcFiniteSliceMap_exists d T W n).exists.choose_spec V)
    (pbcQuotientConstant T d n (op V.left) b ⊥)

private def openSliceForget {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) :
    cbcSliceFunctor T (cbcOpenObject e he) ⋙ cbcOpenSiteFunctor e he ≅
      Over.forget (cbcOpenObject e he) :=
  NatIso.ofComponents (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ V.left.hom = V.hom.left ≫ e
    exact (MorphismProperty.Over.w V.hom).symm))
    (by
      intro V V' f
      apply MorphismProperty.Over.Hom.ext
      change f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left.left
      simp)

private theorem openSliceContinuous {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) :
    (cbcSliceFunctor T (cbcOpenObject e he)).IsContinuous
      ((ProEt.topology T).over (cbcOpenObject e he)) (ProEt.topology W) :=
  cbcSliceFunctor_continuous T (cbcOpenObject e he)

private theorem openSliceCompContinuous {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) :
    (cbcSliceFunctor T (cbcOpenObject e he) ⋙ cbcOpenSiteFunctor e he).IsContinuous
      ((ProEt.topology T).over (cbcOpenObject e he)) (ProEt.topology T) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ (cbcSliceFunctor T (cbcOpenObject e he))
    (cbcOpenSiteFunctor e he) ((ProEt.topology T).over (cbcOpenObject e he))
    (ProEt.topology W) (ProEt.topology T) (openSliceContinuous e he)
    (cbcOpenSiteFunctor_continuous e he)

attribute [local instance] openSliceContinuous openSliceCompContinuous

private theorem finiteOpenSliceSquare {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    (finiteSliceRing d T (cbcOpenObject e he) n).hom ≫
      ((cbcSliceFunctor T (cbcOpenObject e he)).sheafPushforwardContinuous
        CommRingCat.{u + 1} ((ProEt.topology T).over (cbcOpenObject e he))
        (ProEt.topology W)).map (finiteOpenRing d e he n).hom =
    (show (coefficients (cbcFiniteRing d n) T).over (cbcOpenObject e he) ⟶
      ((Functor.sheafPushforwardContinuous
        (cbcSliceFunctor T (cbcOpenObject e he) ⋙ cbcOpenSiteFunctor e he)
        CommRingCat.{u + 1}
          ((ProEt.topology T).over (cbcOpenObject e he)) (ProEt.topology T)).obj
          (coefficients (cbcFiniteRing d n) T)) from
      ⟨Functor.whiskerRight (NatTrans.op (openSliceForget e he).hom)
        (coefficients (cbcFiniteRing d n) T).obj⟩) := by
  let O := cbcOpenObject e he
  let L := Over.forget O
  let C := ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))
  let c := (L.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
    ((ProEt.topology T).over O) (ProEt.topology T)).app C
  apply (cancel_epi c.hom).mp
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    (((cbcSliceFunctor T O ⋙ cbcOpenSiteFunctor e he).sheafPushforwardContinuous
      CommRingCat.{u + 1} ((ProEt.topology T).over O) (ProEt.topology T)).obj
        (coefficients (cbcFiniteRing d n) T)).property
  change (toSheafify _ _ ≫ c.hom.hom) ≫
      (finiteSliceRing d T (cbcOpenObject e he) n).hom.hom ≫
      (Functor.whiskerLeft (cbcSliceFunctor T O).op
        (finiteOpenRing d e he n).hom.hom) =
    (toSheafify _ _ ≫ c.hom.hom) ≫
      Functor.whiskerRight (NatTrans.op (openSliceForget e he).hom)
        (coefficients (cbcFiniteRing d n) T).obj
  erw [L.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
    ((ProEt.topology T).over O) (ProEt.topology T) C]
  ext V b
  change (finiteOpenRing d e he n).hom.hom.app _
    ((finiteSliceRing d T (cbcOpenObject e he) n).hom.hom.app V
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))).app (op V.unop.left) b)) = _
  rw [finiteSliceRing_unit]
  have hc := ConcreteCategory.congr_hom
    (congr_app (finiteOpenRing_unit d e he n)
      (op ((cbcSliceFunctor T (cbcOpenObject e he)).obj V.unop))) b
  have hn := ConcreteCategory.congr_hom
    ((toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))).naturality
      ((openSliceForget e he).hom.app V.unop).op) b
  change (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))).app
      (op ((cbcOpenSiteFunctor e he).obj
        ((cbcSliceFunctor T (cbcOpenObject e he)).obj V.unop))) b =
    (coefficients (cbcFiniteRing d n) T).obj.map
      ((openSliceForget e he).hom.app V.unop).op
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))).app
        (op V.unop.left) b) at hn
  exact hc.trans hn

private theorem finiteSliceRing_projection (T : Scheme.{u}) (W : T.ProEt) (n : ℕ) :
    CbcOpenRingSquare W (cbcCompletedRestriction W d) (finiteSliceRing d T W n)
      (cbcFiniteProjection d T n) (cbcFiniteProjection d W.left n) := by
  let F := (cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
    ((ProEt.topology T).over W) (ProEt.topology W.left)
  let O := (ProEt.topology T).overPullback CommRingCat.{u + 1} W
  have h := (cbcCompletedSliceMap_exists d T W).exists.choose_spec n
  change (cbcCompletedSliceMap d T W) ≫ F.map (pbcAdicProjection W.left d n) =
    O.map (pbcAdicProjection T d n) ≫ cbcFiniteSliceMap d T W n at h
  change O.map (cbcFiniteProjection d T n) ≫ (finiteSliceRing d T W n).hom =
    (cbcCompletedSliceMap d T W) ≫ F.map (cbcFiniteProjection d W.left n)
  dsimp only [cbcFiniteProjection, finiteSliceRing, Functor.mapIso_hom,
    Iso.trans_hom, Iso.symm_hom, cbcFiniteRestriction, asIso_hom]
  change (O.map (pbcAdicProjection T d n ≫ (pbcLevelConstantComparison T d n).inv) ≫
      O.map (pbcLevelConstantComparison T d n).hom) ≫ cbcFiniteSliceMap d T W n ≫
        F.map (pbcLevelConstantComparison W.left d n).inv =
      cbcCompletedSliceMap d T W ≫
        F.map (pbcAdicProjection W.left d n ≫ (pbcLevelConstantComparison W.left d n).inv)
  rw [← O.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    F.map_comp]
  exact (congrArg (fun z ↦ z ≫ F.map (pbcLevelConstantComparison W.left d n).inv)
    h.symm).trans (Category.assoc _ _ _)

attribute [local irreducible] finiteSliceRing

private theorem sliceModulePushforward_isEquivalence
    (T : Scheme.{u}) (W : T.ProEt)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R.over W ≅ cbcSliceRing W S) :
    (SheafOfModules.pushforward.{u + 1} (F := cbcSliceFunctor T W)
      (J := (ProEt.topology T).over W) (K := ProEt.topology W.left)
      (R := (sheafCompose (ProEt.topology W.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
      (S := ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over W)
      ((sheafCompose ((ProEt.topology T).over W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).IsEquivalence := by
  let a := ProEt.sliceEquiv T W
  let := ProEt.sliceDense T W
  have : a.symm.inverse.IsDenseSubsite ((ProEt.topology T).over W)
      (ProEt.topology W.left) := inferInstanceAs
    ((ProEt.sliceEquiv T W).functor.IsDenseSubsite
      ((ProEt.topology T).over W) (ProEt.topology W.left))
  let Rr := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let Sr := (sheafCompose (ProEt.topology W.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let cr : Rr.over W ≅
      (a.functor.sheafPushforwardContinuous RingCat.{u + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).obj Sr :=
    (sheafCompose ((ProEt.topology T).over W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  obtain ⟨q, hq⟩ := ProEt.module_transport (ProEt.topology W.left)
    ((ProEt.topology T).over W) a.symm Sr (Rr.over W) cr
  let P := SheafOfModules.pushforward.{u + 1} (F := cbcSliceFunctor T W)
    (J := (ProEt.topology T).over W) (K := ProEt.topology W.left)
    (R := Sr) (S := Rr.over W)
    ((sheafCompose ((ProEt.topology T).over W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)
  let E : q.functor ≅ P :=
    ((SheafOfModules.fullyFaithfulForget _).whiskeringRight _).preimageIso (eqToIso hq)
  exact Functor.isEquivalence_of_iso E

private def finiteModuleToSlice {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    ProEtale.StrictTower.Modules (cbcFiniteRing d n) W ⥤
      SheafOfModules.{u + 1} (((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (coefficients (cbcFiniteRing d n) T)).over (cbcOpenObject e he)) := by
  have : (cbcSliceFunctor T (cbcOpenObject e he)).IsContinuous
      ((ProEt.topology T).over (cbcOpenObject e he)) (ProEt.topology W) :=
    cbcSliceFunctor_continuous T (cbcOpenObject e he)
  exact SheafOfModules.pushforward.{u + 1} (F := cbcSliceFunctor T (cbcOpenObject e he))
    (J := (ProEt.topology T).over (cbcOpenObject e he)) (K := ProEt.topology W)
    (R := (sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients (cbcFiniteRing d n) W))
    (S := ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficients (cbcFiniteRing d n) T)).over (cbcOpenObject e he))
    ((sheafCompose ((ProEt.topology T).over (cbcOpenObject e he))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (finiteSliceRing d T (cbcOpenObject e he) n).hom)

private def finiteRestrictionToSlice {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    (SheafOfModules.pushforward.{u + 1} (F := cbcOpenSiteFunctor e he)
      (J := ProEt.topology W) (K := ProEt.topology T)
      (R := (sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (coefficients (cbcFiniteRing d n) T))
      (S := (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (coefficients (cbcFiniteRing d n) W))
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (finiteOpenRing d e he n).hom)) ⋙ finiteModuleToSlice d e he n ≅
      SheafOfModules.overFunctor.{u + 1}
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficients (cbcFiniteRing d n) T)) (cbcOpenObject e he) := by
  have : (cbcSliceFunctor T (cbcOpenObject e he)).IsContinuous
      ((ProEt.topology T).over (cbcOpenObject e he)) (ProEt.topology W) :=
    cbcSliceFunctor_continuous T (cbcOpenObject e he)
  have : (cbcOpenSiteFunctor e he).IsContinuous (ProEt.topology W) (ProEt.topology T) :=
    cbcOpenSiteFunctor_continuous e he
  have : (cbcSliceFunctor T (cbcOpenObject e he) ⋙ cbcOpenSiteFunctor e he).IsContinuous
      ((ProEt.topology T).over (cbcOpenObject e he)) (ProEt.topology T) :=
    Functor.isContinuous_comp _ _ _ (ProEt.topology W) _
  let S := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients (cbcFiniteRing d n) T)
  let RW := (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients (cbcFiniteRing d n) W)
  let φ : S.over (cbcOpenObject e he) ⟶
      ((cbcSliceFunctor T (cbcOpenObject e he)).sheafPushforwardContinuous RingCat.{u + 1}
        ((ProEt.topology T).over (cbcOpenObject e he)) (ProEt.topology W)).obj RW :=
    (sheafCompose ((ProEt.topology T).over (cbcOpenObject e he))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (finiteSliceRing d T (cbcOpenObject e he) n).hom
  let ψ : RW ⟶ ((cbcOpenSiteFunctor e he).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology W) (ProEt.topology T)).obj S := (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (finiteOpenRing d e he n).hom
  refine SheafOfModules.pushforwardComp (F := cbcSliceFunctor T (cbcOpenObject e he))
    (G := cbcOpenSiteFunctor e he) (J := (ProEt.topology T).over (cbcOpenObject e he))
    (K := ProEt.topology W) (K' := ProEt.topology T) φ ψ ≪≫ ?_
  refine (SheafOfModules.pushforwardCongr ?_) ≪≫
    (SheafOfModules.pushforwardNatIso (F := cbcSliceFunctor T (cbcOpenObject e he) ⋙
      cbcOpenSiteFunctor e he) (G := Over.forget (cbcOpenObject e he))
      (𝟙 (S.over (cbcOpenObject e he))) (openSliceForget e he)).symm
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  exact congrArg (fun z ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    (z.hom.app V)) (finiteOpenSliceSquare d e he n)

private theorem openObject_subsingleton {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (V : T.ProEt) :
    Subsingleton (V ⟶ cbcOpenObject e he) := by
  let := he
  constructor
  intro f g
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono e).mp
  exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm

private def sliceExtension_fullyFaithful {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    (SheafOfModules.localizedSystemExtension.{u + 1, u, 0} R
      (cbcOpenObject e he)).FullyFaithful := by
  let Rr := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let a := SheafOfModules.extensionSheafAdjunction Rr (cbcOpenObject e he)
  have h (M : SheafOfModules.{u + 1} (Rr.over (cbcOpenObject e he))) :
      IsIso (a.unit.app M) :=
    SheafOfModules.extensionSheafAdjunction_unit_isIso Rr (cbcOpenObject e he)
      (openObject_subsingleton e he) M
  have : IsIso a.unit := NatIso.isIso_of_isIso_app _
  exact a.fullyFaithfulLOfIsIsoUnit

private def finiteExtensionAdjunction {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    cbcRingedOpenExtension (cbcOpenObject e he)
      (finiteSliceRing d T (cbcOpenObject e he) n) ⊣ modulePullback (cbcFiniteRing d n) e := by
  have : (finiteModuleToSlice d e he n).IsEquivalence :=
    sliceModulePushforward_isEquivalence T (cbcOpenObject e he)
      (finiteSliceRing d T (cbcOpenObject e he) n)
  let Q := (finiteModuleToSlice d e he n).asEquivalence
  let R := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients (cbcFiniteRing d n) T)
  let a := AlgebraicGeometry.ProEtale.openAdjunctionTransport Q _ _ _
    (SheafOfModules.extensionSheafAdjunction R (cbcOpenObject e he))
    (finiteRestrictionToSlice d e he n)
  exact a.ofNatIsoRight (finiteOpenModel d e he n).symm

private def finiteExtensionComparison {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :=
  (finiteExtensionAdjunction d e he n).leftAdjointUniq
    (@moduleJAdj.{u} (cbcFiniteRing d n) _ W T e he)

private theorem finiteExtension_unit_isIso {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    IsIso (@moduleJAdj.{u} (cbcFiniteRing d n) _ W T e he).unit := by
  have : (finiteModuleToSlice d e he n).IsEquivalence :=
    sliceModulePushforward_isEquivalence T (cbcOpenObject e he)
      (finiteSliceRing d T (cbcOpenObject e he) n)
  let F := cbcRingedOpenExtension (cbcOpenObject e he)
    (finiteSliceRing d T (cbcOpenObject e he) n)
  let hF : F.FullyFaithful := Functor.FullyFaithful.comp
    (Functor.FullyFaithful.ofFullyFaithful (finiteModuleToSlice d e he n))
    (sliceExtension_fullyFaithful e he (coefficients (cbcFiniteRing d n) T))
  let hJ := hF.ofIso (finiteExtensionComparison d e he n)
  let := hJ.full
  let := hJ.faithful
  infer_instance

private def completedExtension_fullyFaithful {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) : (cbcOpenShriek d e he).FullyFaithful := by
  have : (cbcModuleToSlice d T (cbcOpenObject e he)).IsEquivalence :=
    sliceModulePushforward_isEquivalence T (cbcOpenObject e he)
      (cbcCompletedRestriction (cbcOpenObject e he) d)
  exact Functor.FullyFaithful.comp
    (Functor.FullyFaithful.ofFullyFaithful (cbcModuleToSlice d T (cbcOpenObject e he)))
    (sliceExtension_fullyFaithful e he (pbcAdicCompletion T d))

/-- The normalized open-extension comparison is invertible.
Source: Stacks 03DI (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: the finite extension unit is invertible, and the adjunct of the specified
mate is this unit followed by the fixed open-restriction isomorphism. The existing
ringed-slice scalar comparison places its target in the essential image of the
fully faithful completed extension. Its counit is therefore invertible, and the
adjunction formula expresses the mate as a composite of two isomorphisms. -/
@[instance] theorem cbcFiniteOpenRes_isIso {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    IsIso (cbcFiniteOpenRes d e he n) := by
  let := he
  let a := @moduleJAdj.{u} (cbcFiniteRing d n) _ W T e he
  let b := cbcOpenAdjunction d e he
  have := finiteExtension_unit_isIso d e he n
  let hb := completedExtension_fullyFaithful d e he
  let := hb.full
  let := hb.faithful
  let θ := cbcOpenRestrictIso (cbcOpenObject e he)
    (cbcCompletedRestriction (cbcOpenObject e he) d)
    (finiteSliceRing d T (cbcOpenObject e he) n)
    (cbcFiniteProjection d T n) (cbcFiniteProjection d W n)
    (finiteSliceRing_projection d T (cbcOpenObject e he) n)
  let χ := θ ≪≫ Functor.isoWhiskerRight (finiteExtensionComparison d e he n)
    (cbcFiniteRes d T n)
  have h (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) W) :
      IsIso ((cbcFiniteOpenRes d e he n).app M) := by
    let f := (cbcFiniteOpenRes d e he n).app M
    have hf : b.homEquiv _ _ f =
        (cbcFiniteRes d W n).map (a.unit.app M) ≫
          (cbcFiniteOpenRestriction d e he n).hom.app ((moduleJ (cbcFiniteRing d n) e).obj M) := by
      rw [Adjunction.homEquiv_unit]
      exact (unit_mateEquiv_symm a b
        (TwoSquare.mk _ _ _ _ (cbcFiniteOpenRestriction d e he n).hom) M).symm
    have hi : IsIso (b.homEquiv _ _ f) := by
      rw [hf]
      infer_instance
    have hs : (cbcOpenShriek d e he).essImage
        (((moduleJ (cbcFiniteRing d n) e) ⋙ cbcFiniteRes d T n).obj M) :=
      ⟨(cbcFiniteRes d W n).obj M, ⟨χ.app M⟩⟩
    have : IsIso (b.counit.app _) := b.isIso_counit_app_iff_mem_essImage.mpr hs
    have heq : f = (cbcOpenShriek d e he).map (b.homEquiv _ _ f) ≫ b.counit.app _ :=
      ((b.homEquiv _ _).symm_apply_apply f).symm
    change IsIso f
    rw [heq]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Finite coordinates for the source of the ordinary exchange, built by the
specified open and pullback mates.
Source: Stacks 03DI, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteSourceRes (n : ℕ) :
    cbcFiniteRes d U n ⋙ cbcOpenShriek d j sq.isOpenImmersion ⋙ completedModulePullback g d ≅
      (@moduleJ.{u} (cbcFiniteRing d n) _ U X j sq.isOpenImmersion) ⋙
        modulePullback (cbcFiniteRing d n) g ⋙ cbcFiniteRes d X' n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (cbcFiniteOpenRes d j sq.isOpenImmersion n)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (cbcFinitePullRes d g n))

/-- Finite coordinates for the target, in the prescribed pullback-then-open order.
Source: Stacks 03DI, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteTargetRes (n : ℕ) :
    cbcFiniteRes d U n ⋙ completedModulePullback gU d ⋙
        cbcOpenShriek d j' sq.isOpenImmersion' ≅
      modulePullback (cbcFiniteRing d n) gU ⋙
        (@moduleJ.{u} (cbcFiniteRing d n) _ U' X' j' sq.isOpenImmersion') ⋙
          cbcFiniteRes d X' n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (cbcFinitePullRes d gU n)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (cbcFiniteOpenRes d j' sq.isOpenImmersion' n))

/-- Reduction to finite constant coefficients, using the existing scalar extension
and the fixed constant-section coefficient isomorphism.
Source: Stacks 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteReductionModule (T : Scheme.{u}) (n : ℕ) :=
  reductionChange T (pbcAdicProjection T d n) ⋙
    pbcRestrict (pbcLevelConstantComparison T d n).hom

/-- Finite reduction followed by coefficient restriction is additive.
Source: Stacks 03EK, 099N
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: sheafified scalar extension and scalar restriction both preserve sums of
morphisms. Composing their sum equations proves additivity. -/
@[instance] theorem cbcFiniteReductionModule_additive (T : Scheme.{u}) (n : ℕ) :
    (cbcFiniteReductionModule d T n).Additive := by
  unfold cbcFiniteReductionModule
  infer_instance

/-- The finite quotient object in its own constant coefficient derived category.
Source: Stacks 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteReduction (T : Scheme.{u}) (n : ℕ) :=
  reductionDerivedChange T (pbcAdicProjection T d n) ⋙
    pbcDerivedRestrict (pbcLevelConstantComparison T d n).hom

/-- Reexpressing an ordinary reduction tower level in constant finite coordinates
leaves every section unchanged and only transports its coefficient action.
Source: Stacks 099N (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: the projection followed by the inverse constant comparison is the specified
completed action. Restricting successively along the comparison and its inverse
cancels, so identity sections give the unique natural isomorphism. -/
theorem cbcFiniteLevel_existsUnique (T : Scheme.{u}) (n : ℕ) :
    ∃! e : completedReductionModuleTowerFunctor T d ⋙
          (CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj (op n) ≅
        cbcFiniteReductionModule d T n ⋙ cbcFiniteRes d T n,
      ∀ (M : pbcModules T (pbcAdicCompletion T d)) (V : T.ProEtᵒᵖ)
        (x : ((reductionChange T (pbcAdicProjection T d n)).obj M).val.obj V),
        (e.hom.app M).val.app V x = x := by
  let φ := cbcFiniteProjection d T n
  let ψ := (pbcLevelConstantComparison T d n).hom
  let χ := pbcAdicProjection T d n
  have h : φ ≫ ψ = χ := by
    simp [φ, ψ, χ, cbcFiniteProjection]
  have hV (V : T.ProEtᵒᵖ) : (χ.hom.app V).hom =
      (ψ.hom.app V).hom.comp (φ.hom.app V).hom := by
    exact congrArg (fun f ↦ (f.hom.app V).hom) h.symm
  let eM (M : pbcModules T (pbcAdicCompletion T d)) :
      ((completedReductionModuleTowerFunctor T d).obj M).obj (op n) ≅
        ((cbcFiniteReductionModule d T n ⋙ cbcFiniteRes d T n).obj M) :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        ModuleCat.restrictScalarsComp'App (φ.hom.app V).hom (ψ.hom.app V).hom
          (χ.hom.app V).hom (hV V)
          (((reductionChange T χ).obj M).val.obj V))
        (fun {V W} f ↦ by ext x; rfl))
  let e : completedReductionModuleTowerFunctor T d ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj (op n) ≅
        cbcFiniteReductionModule d T n ⋙ cbcFiniteRes d T n :=
    NatIso.ofComponents eM (fun f ↦ by ext V x; rfl)
  refine ⟨e, fun _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  ext M V x
  exact he' M V x

/-- The finite coordinate change fixed by identity on sections.
Source: Stacks 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
@[irreducible] def cbcFiniteLevel (T : Scheme.{u}) (n : ℕ) :=
  (cbcFiniteLevel_existsUnique d T n).exists.choose

/-- The finite source functor, including the completed action through the projection.
Source: Stacks 03DI, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteSource (n : ℕ) :=
  (@moduleJ.{u} (cbcFiniteRing d n) _ U X j sq.isOpenImmersion) ⋙
    modulePullback (cbcFiniteRing d n) g ⋙ cbcFiniteRes d X' n

/-- The finite target functor in the pullback-then-extension order.
Source: Stacks 03DI, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteTarget (n : ℕ) :=
  modulePullback (cbcFiniteRing d n) gU ⋙
    (@moduleJ.{u} (cbcFiniteRing d n) _ U' X' j' sq.isOpenImmersion') ⋙
      cbcFiniteRes d X' n

/-- Both finite source and target are exact and additive.
Source: Stacks 03DI, 03DJ, 03EK
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: open extension and finite constant pullback are exact and additive, as
is scalar restriction. Compose these properties in the indicated order. -/
@[instance] theorem cbcFiniteSource_additive (n : ℕ) :
    (cbcFiniteSource d sq n).Additive := by
  unfold cbcFiniteSource cbcFiniteRes
  infer_instance

/-- Exactness of the finite source, checked before derived localization.
Source: Stacks 03DJ, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: compose exact open extension, finite pullback and scalar restriction. -/
@[instance] theorem cbcFiniteSource_limits (n : ℕ) :
    PreservesFiniteLimits (cbcFiniteSource d sq n) := by
  unfold cbcFiniteSource cbcFiniteRes
  infer_instance

/-- The finite source preserves cokernels and finite sums.
Source: Stacks 03DI, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: all three functors preserve finite colimits, hence so does their composite. -/
@[instance] theorem cbcFiniteSource_colimits (n : ℕ) :
    PreservesFiniteColimits (cbcFiniteSource d sq n) := by
  unfold cbcFiniteSource cbcFiniteRes
  infer_instance

/-- Additivity of the finite target.
Source: Stacks 03DI, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: finite pullback, open extension and scalar restriction are additive. -/
@[instance] theorem cbcFiniteTarget_additive (n : ℕ) :
    (cbcFiniteTarget d sq n).Additive := by
  unfold cbcFiniteTarget cbcFiniteRes
  infer_instance

/-- Exactness of the finite target on kernels.
Source: Stacks 03DJ, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: each of the three factors preserves finite limits. -/
@[instance] theorem cbcFiniteTarget_limits (n : ℕ) :
    PreservesFiniteLimits (cbcFiniteTarget d sq n) := by
  unfold cbcFiniteTarget cbcFiniteRes
  infer_instance

/-- Exactness of the finite target on cokernels.
Source: Stacks 03DI, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: each of the three factors preserves finite colimits. -/
@[instance] theorem cbcFiniteTarget_colimits (n : ℕ) :
    PreservesFiniteColimits (cbcFiniteTarget d sq n) := by
  unfold cbcFiniteTarget cbcFiniteRes
  infer_instance

/-- Finite reduction followed by the finite source preserves zero morphisms.
Source: Stacks 03DI, 03EK, 099N
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: both functors are additive. Their sum equations imply that their composite
sends the zero map to zero, including the completed scalar restriction. -/
theorem cbcFiniteSourceModel_preservesZeroMorphisms (n : ℕ) :
    (cbcFiniteReductionModule d U n ⋙ cbcFiniteSource d sq n).PreservesZeroMorphisms := by
  have := cbcFiniteReductionModule_additive d U n
  have := cbcFiniteSource_additive d sq n
  exact Functor.preservesZeroMorphisms_of_additive _

/-- Finite reduction followed by the finite target preserves zero morphisms.
Source: Stacks 03DI, 03EK, 099N
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: compose the zero-map equations of finite scalar extension, pullback,
open extension and scalar restriction. -/
theorem cbcFiniteTargetModel_preservesZeroMorphisms (n : ℕ) :
    (cbcFiniteReductionModule d U n ⋙ cbcFiniteTarget d sq n).PreservesZeroMorphisms := by
  have := cbcFiniteReductionModule_additive d U n
  have := cbcFiniteTarget_additive d sq n
  exact Functor.preservesZeroMorphisms_of_additive _

/-- The evaluated source model preserves zero morphisms.
Source: Stacks 03DI, 03EK, 099N
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: reduction is additive levelwise, as are open extension and module pullback.
Evaluation preserves zero maps. Their composite therefore sends zero to zero. -/
theorem cbcSourceLevel_preservesZeroMorphisms (n : ℕ) :
    (completedReductionModuleTowerFunctor U d ⋙ cbcStrictOpenModule d j sq.isOpenImmersion ⋙
      completedTowerModulePullback g d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj
          (op n)).PreservesZeroMorphisms := by
  have := completedReductionModuleTowerFunctor_additive U d
  have := completedTowerModulePullback_additive g d
  have := cbcStrictOpenModule_additive d j sq.isOpenImmersion
  exact Functor.preservesZeroMorphisms_of_additive _

/-- The evaluated target model preserves zero morphisms.
Source: Stacks 03DI, 03EK, 099N
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: each constituent sends zero morphisms to zero, including the evaluation.
Composing those equations in pullback-then-open order proves the assertion. -/
theorem cbcTargetLevel_preservesZeroMorphisms (n : ℕ) :
    (completedReductionModuleTowerFunctor U d ⋙ completedTowerModulePullback gU d ⋙
      cbcStrictOpenModule d j' sq.isOpenImmersion' ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj
          (op n)).PreservesZeroMorphisms := by
  have := completedReductionModuleTowerFunctor_additive U d
  have := completedTowerModulePullback_additive gU d
  have := cbcStrictOpenModule_additive d j' sq.isOpenImmersion'
  exact Functor.preservesZeroMorphisms_of_additive _

/-- The ordinary finite-coordinate source comparison: first change the reduction
level's coordinates, then use the fixed scalar/open/pullback mates.
Source: Stacks 03DI, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcSourceLevel (n : ℕ) :
    completedReductionModuleTowerFunctor U d ⋙ cbcStrictOpenModule d j sq.isOpenImmersion ⋙
        completedTowerModulePullback g d ⋙
          (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj (op n) ≅
      cbcFiniteReductionModule d U n ⋙ cbcFiniteSource d sq n :=
  Functor.isoWhiskerRight (cbcFiniteLevel d U n)
      (cbcOpenShriek d j sq.isOpenImmersion ⋙ completedModulePullback g d) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (cbcFiniteSourceRes d sq n)

/-- The analogous ordinary target comparison, with the identical finite coordinate change.
Source: Stacks 03DI, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcTargetLevel (n : ℕ) :
    completedReductionModuleTowerFunctor U d ⋙ completedTowerModulePullback gU d ⋙
        cbcStrictOpenModule d j' sq.isOpenImmersion' ⋙
          (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj (op n) ≅
      cbcFiniteReductionModule d U n ⋙ cbcFiniteTarget d sq n :=
  Functor.isoWhiskerRight (cbcFiniteLevel d U n)
      (completedModulePullback gU d ⋙ cbcOpenShriek d j' sq.isOpenImmersion') ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (cbcFiniteTargetRes d sq n)

/-- The actual universal reduction counit on cochain representatives.
Source: Stacks 06XN (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcReductionModelMap (T : Scheme.{u})
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    (completedReductionTower T d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((completedReductionModuleTowerFunctor T d).mapHomologicalComplex (.up ℤ)).obj P) :=
  Functor.leftDerivedCounitOnComplex (completedReductionModuleTowerFunctor T d)
    (completedReductionTower T d) (completedReductionTowerCounit d T) P

/-- Source comparison to its ordinary strict model, using only the universal counits.
Source: Stacks 06XN (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcSourceModelMap (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ) :
    (completedReductionTower U d ⋙ cbcStrictOpen d j sq.isOpenImmersion ⋙
      completedTowerPullback g d).obj (DerivedCategory.Q.obj P) ⟶
    DerivedCategory.Q.obj
      (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
        (((cbcStrictOpenModule d j sq.isOpenImmersion).mapHomologicalComplex (.up ℤ)).obj
          (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj P))) :=
  (completedTowerPullback g d).map
    ((cbcStrictOpen d j sq.isOpenImmersion).map (cbcReductionModelMap d U P) ≫
      (cbcStrictOpenModule d j sq.isOpenImmersion).mapDerivedCategoryFactors.hom.app
        (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj P)) ≫
    completedTowerPullbackComplexCounit g d
      (((cbcStrictOpenModule d j sq.isOpenImmersion).mapHomologicalComplex (.up ℤ)).obj
        (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj P))

/-- Target comparison to the same ordinary strict model convention.
Source: Stacks 06XN (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcTargetModelMap (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ) :
    (completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
      cbcStrictOpen d j' sq.isOpenImmersion').obj (DerivedCategory.Q.obj P) ⟶
    DerivedCategory.Q.obj
      (((cbcStrictOpenModule d j' sq.isOpenImmersion').mapHomologicalComplex (.up ℤ)).obj
        (((completedTowerModulePullback gU d).mapHomologicalComplex (.up ℤ)).obj
          (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj P))) :=
  (cbcStrictOpen d j' sq.isOpenImmersion').map
    ((completedTowerPullback gU d).map (cbcReductionModelMap d U P) ≫
      completedTowerPullbackComplexCounit gU d
        (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj P)) ≫
    (cbcStrictOpenModule d j' sq.isOpenImmersion').mapDerivedCategoryFactors.hom.app
      (((completedTowerModulePullback gU d).mapHomologicalComplex (.up ℤ)).obj
        (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj P))

end AlgebraicGeometry.Scheme
