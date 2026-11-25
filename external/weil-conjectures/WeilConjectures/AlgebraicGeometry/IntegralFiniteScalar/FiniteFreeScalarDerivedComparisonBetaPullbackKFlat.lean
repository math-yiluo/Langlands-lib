/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import all WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonBetaConstruction
import all WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryTensorSquare
import all WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarTensorPullComputation
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarRestrictedPullbackCounit
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarNormalizedBetaComputation
import WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeScalarPointComparison
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarTotalPullbackSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteFreeScalarOrdinaryTensorPullback

/-! # Pullback compatibility of normalized beta on K-flat representatives
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

private instance ring_comm (Λ : ScalarSixRing.{u}) : IsCommMonObj Λ.X := Λ.comm

private instance map_monoid {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    IsMonHom a.hom.hom := a.hom.isMonHom_hom

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  DerivedCategory.monoidalClosed Mod.monoidalClosed Sheaf.monoidalCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint Mod.monoidalCategoryStruct
  profinitePointModuleForgetPullbackIso Mod.extendScalarsIsoComapInv

attribute [local irreducible] betaTotalNatIso betaOrdinary betaTargetIso
  betaRestrictedCounit betaScalarCounit

open Lean Meta Elab Tactic
-- Build explicit congruences so kernel conversion does not repeatedly traverse
-- equivalent sheaf structures carrying different proof witnesses.
private def structuralDefeq : Nat → Expr → Expr → MetaM Expr
  | 0, _, _ => throwError "structural conversion depth exhausted"
  | n + 1, a, b => do
    let a ← instantiateMVars a
    let b ← instantiateMVars b
    let a := a.consumeMData
    let b := b.consumeMData
    if a == b then return ← mkHEqRefl a
    if (← isProof a) && (← isProof b) then
      return ← mkAppM ``proof_irrel_heq #[a, b]
    for d in ← getLCtx do
      let dt ← instantiateMVars d.type
      if let some (_, x, _, y) := dt.consumeMData.heq? then
        if x == a && y == b then return d.toExpr
        if x == b && y == a then return ← mkAppM ``HEq.symm #[d.toExpr]
      if let some (_, x, y) := dt.consumeMData.eq? then
        if x == a && y == b then return ← mkHEqOfEq d.toExpr
        if x == b && y == a then
          return ← mkHEqOfEq (← mkAppM ``Eq.symm #[d.toExpr])
    if a.isLambda && b.isLambda then
      let hd ← mkEqOfHEq (← structuralDefeq n a.bindingDomain! b.bindingDomain!)
      return ← withLocalDeclD `x a.bindingDomain! fun x ↦ do
        withLocalDeclD `y b.bindingDomain! fun y ↦ do
          withLocalDeclD `hxy (← mkHEq x y) fun hxy ↦ do
            let hb ← structuralDefeq n (mkApp a x) (mkApp b y)
            let hf ← mkLambdaFVars #[x, y, hxy] hb
            mkAppM ``Function.hfunext #[hd, hf]
    let f := a.getAppFn
    let g := b.getAppFn
    let aa := a.getAppArgs
    let bb := b.getAppArgs
    if f == g && aa.size == bb.size && aa.size > 0 then
      try
        let thm ← mkHCongrWithArity f aa.size
        let mut args := #[]
        for x in aa, y in bb, kind in thm.argKinds do
          let h ← structuralDefeq n x y
          match kind with
          | .eq => args := args ++ #[x, y, ← mkEqOfHEq h]
          | .heq => args := args ++ #[x, y, h]
          | _ => throwError "unexpected congruence argument kind"
        let p := mkAppN thm.proof args
        if (← inferType p).isHEq then return p
        else return ← mkHEqOfEq p
      catch _ => pure ()
    let a' ← withTransparency .all (whnf a)
    let b' ← withTransparency .all (whnf b)
    if a' == a && b' == b then throwError "no progress: {a} versus {b}"
    structuralDefeq n a' b'

private def structuralCast (g : MVarId) (pf : Expr) : MetaM Unit := do
  let h ← structuralDefeq 200 (← inferType pf) (← g.getType)
  g.assign (← mkAppM ``Eq.mp #[← mkEqOfHEq h, pf])

private def structuralRefl (g : MVarId) : MetaM Unit := do
  let some (_, lhs, _) := (← g.getType).eq? |
    throwError "structural reflexivity expects an equality, got {← g.getType}"
  structuralCast g (← mkEqRefl lhs)

-- Comparing normalized total tensors traverses several monoidal module structures.
private lemma normalized_beta_computes
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)) (Z : Scheme.{u})
    (β : tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
      scalarSixChange a Z ⋙ restriction a Z)
    (hβ : AugmentationNormalized a S t Z β)
    (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Z) ℤ)
    (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) :
    β.hom.app (DerivedCategory.Q.obj C) ≫ (betaRestrictedCounit a Z).app C =
      Functor.LaxMonoidal.μ DerivedCategory.Q (complex Λ S Z) C ≫
        DerivedCategory.Q.map (HomologicalComplex.tensorHom (augmentation Λ S Z) (𝟙 C)) ≫
        DerivedCategory.Q.map ((betaTotalNatIso a S t Z).hom.app C) := by
  simpa only [betaRestrictedCounit, betaScalarCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, betaMap, Iso.app_hom] using
    finiteFreeScalar_normalizedBeta_computes a S t Z β hβ C hC
      (fun M ↦ (betaOrdinary a Z).app M) (fun M ↦ betaOrdinary_hom a Z M)
      ((betaTotalNatIso a S t Z).app C) (fun n ↦ betaTotalIso_summand a S t Z C n)

-- Unpack coefficient data before comparing the specified point isomorphisms.
private lemma point_comp_underlying (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : PointModules Λ) :
    (profinitePointModuleForgetPullbackIso Λ.X f).inv.app ((pointPull Λ Y).obj M) ≫
      ((pointModuleComp Λ f).hom.app M).hom =
      (upperStarFromPointComp f).hom.app M.X := by
  have h := finiteFreeScalar_pointComparison_underlying Λ.X f M
  dsimp only [pointModuleComp, pointPull, sfbPullbackFromPoint,
    CondensedRing.upperStarFromPointMod] at h ⊢
  run_tac withMainContext do
    structuralCast (← getMainGoal) (← getLocalDeclFromUserName `h).toExpr

private lemma coefficientModuleIso_hom {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (Z : Scheme.{u}) :
    (coefficientModuleIso a Z).hom.hom = 𝟙 ((sfbPullbackFromPoint Z).obj Λ'.X) := by
  run_tac withMainContext do structuralRefl (← getMainGoal)

private lemma idSquare {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {M : A} {N : B} (a : F.obj M ⟶ N) :
    F.map (𝟙 M) ≫ a = a ≫ 𝟙 N := by simp

-- Compare the specified point and regular-module coefficient identifications.
private lemma point_coefficient_pull {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ.X f).map (coefficientModuleIso a Y).hom ≫
      (residueOrdinaryRestrictedRegularPullIso Λ.X Λ'.X a.hom.hom f).hom =
    (pointModuleComp Λ f).hom.app ((Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)) ≫
      (coefficientModuleIso a X).hom := by
  apply Mod.hom_ext
  apply (cancel_epi ((profinitePointModuleForgetPullbackIso Λ.X f).inv.app
    ((pointPull Λ Y).obj ((Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))))).1
  simp only [Mod.comp_hom']
  have hn := (profinitePointModuleForgetPullbackIso Λ.X f).inv.naturality
    (coefficientModuleIso a Y).hom
  dsimp only [Functor.comp_map, Mod.forget] at hn
  rw [← Category.assoc, ← hn, Category.assoc]
  erw [coefficient_pull_hom Λ.X Λ'.X a.hom.hom f]
  rw [← Category.assoc, point_comp_underlying]
  erw [coefficientModuleIso_hom, coefficientModuleIso_hom]
  have h0 := idSquare (ProEtale.upperStar Ab.{u + 1} f) (condensedPullbackHom Λ'.X f)
  run_tac withMainContext do
    structuralCast (← getMainGoal) (← getLocalDeclFromUserName `h0).toExpr

-- Restriction of the ordinary extension square agrees with balanced tensor pullback.
private lemma ordinary_tensor_pull {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleRingedComparison.internalModules Λ.X Y) :
    let F := CondensedRing.upperStar Λ.X f
    F.map ((betaOrdinary a Y).hom.app M) ≫
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
        ((Mod.extendScalars (betaMap a Y)).obj M) ≫
      (Mod.comap (betaMap a X)).map
        ((pullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app M) =
    Functor.OplaxMonoidal.δ F (betaCoefficient a Y) M ≫
      (residueOrdinaryRestrictedRegularPullIso Λ.X Λ'.X a.hom.hom f).hom ▷ F.obj M ≫
      (betaOrdinary a X).hom.app (F.obj M) := by
  dsimp only
  have hk (Z : Scheme.{u}) :
      (betaOrdinary a Z).hom = (Mod.extendComapTensorIso (betaMap a Z)).inv := by
    apply NatTrans.ext
    funext M
    apply Mod.hom_ext
    simp only [betaOrdinary, Mod.KFlatScalarTower.extendTensorNatIso,
      Mod.KFlatScalarTower.extendTensorIso, Mod.extendComapTensorIso, Iso.symm_hom,
      NatIso.ofComponents_inv_app, Mod.isoMk_inv_hom]
  rw [hk, hk]
  rw [ModuleRingedComparison.internalPullOplax_eq_canonical Λ.X f]
  simpa only [betaMap, betaCoefficient] using
    finiteFreeScalar_ordinaryTensor_pullback Λ.X Λ'.X a.hom.hom f M

-- The explicit component formula avoids conversion through the full complex isomorphism.
private lemma pointComplexComp_hom_f (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (C : CochainComplex (PointModules Λ) ℤ) (n : ℤ) :
    (pointComplexComp Λ f C).hom.f n = (pointModuleComp Λ f).hom.app (C.X n) := by
  run_tac withMainContext do structuralRefl (← getMainGoal)

-- Establish the concrete module naturality formula before substituting chosen complex terms.
private lemma pointModuleComp_naturality (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : PointModules Λ} (g : M ⟶ N) :
    (CondensedRing.upperStar Λ.X f).map ((pointPull Λ Y).map g) ≫
        (pointModuleComp Λ f).hom.app N =
      (pointModuleComp Λ f).hom.app M ≫ (pointPull Λ X).map g := by
  have h := (pointModuleComp Λ f).hom.naturality g
  dsimp only [Functor.comp_map] at h
  run_tac withMainContext do
    structuralCast (← getMainGoal) (← getLocalDeclFromUserName `h).toExpr

private lemma mapped_coefficient_square
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {M N P : A} {U V W : B} (g : M ⟶ N) (c : N ⟶ P)
    (r : F.obj P ⟶ W) (eM : F.obj M ⟶ U) (eN : F.obj N ⟶ V)
    (gX : U ⟶ V) (cX : V ⟶ W)
    (hC : F.map c ≫ r = eN ≫ cX) (hN : F.map g ≫ eN = eM ≫ gX) :
    F.map (g ≫ c) ≫ r = eM ≫ (gX ≫ cX) := by
  rw [Functor.map_comp, Category.assoc, hC, ← Category.assoc, hN, Category.assoc]

-- Compute naturality before substituting the single-complex component.
private lemma point_ordinary_coefficient {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : PointModules Λ)
    (g : M ⟶ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)) :
    (CondensedRing.upperStar Λ.X f).map
        ((pointPull Λ Y).map g ≫ (coefficientModuleIso a Y).hom) ≫
      (residueOrdinaryRestrictedRegularPullIso Λ.X Λ'.X a.hom.hom f).hom =
    (pointModuleComp Λ f).hom.app M ≫
      ((pointPull Λ X).map g ≫ (coefficientModuleIso a X).hom) := by
  refine mapped_coefficient_square (CondensedRing.upperStar Λ.X f)
    ((pointPull Λ Y).map g) (coefficientModuleIso a Y).hom
    (residueOrdinaryRestrictedRegularPullIso Λ.X Λ'.X a.hom.hom f).hom
    ((pointModuleComp Λ f).hom.app M)
    ((pointModuleComp Λ f).hom.app ((Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)))
    ((pointPull Λ X).map g) (coefficientModuleIso a X).hom ?_ ?_
  · have h := point_coefficient_pull a f
    run_tac withMainContext do
      structuralCast (← getMainGoal) (← getLocalDeclFromUserName `h).toExpr
  · have h := pointModuleComp_naturality Λ f g
    run_tac withMainContext do
      structuralCast (← getMainGoal) (← getLocalDeclFromUserName `h).toExpr

private lemma mapIso_composite_hom
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {M N P : A} {W : B} (s : M ≅ N) (t : N ≅ P) (c : F.obj P ≅ W) :
    (F.mapIso s ≪≫ F.mapIso t ≪≫ c).hom = F.map (s.hom ≫ t.hom) ≫ c.hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
private lemma coefficient_square_under_iso
    {A B C : Type*} [Category A] [Category B] [Category C]
    (P : A ⥤ B) (Q : A ⥤ C) (F : B ⥤ C)
    {M N R : A} {U : B} {V : C} (s : M ≅ N) (t : N ≅ R)
    (cY : P.obj R ≅ U) (cX : Q.obj R ≅ V) (r : F.obj U ⟶ V)
    (e : F.obj (P.obj M) ⟶ Q.obj M)
    (h : F.map (P.map (s.hom ≫ t.hom) ≫ cY.hom) ≫ r =
      e ≫ (Q.map (s.hom ≫ t.hom) ≫ cX.hom)) :
    F.map (P.mapIso s ≪≫ P.mapIso t ≪≫ cY).hom ≫ r =
      e ≫ (Q.mapIso s ≪≫ Q.mapIso t ≪≫ cX).hom := by
  simpa only [mapIso_composite_hom] using h

private lemma targetZeroIso_hom_comp {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)) (Z : Scheme.{u}) :
    (targetZeroIso a S t Z).hom =
      (pointPull Λ Z).map
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃).hom ≫ t.hom) ≫
        (coefficientModuleIso a Z).hom := by
  simp only [targetZeroIso, mapIso_composite_hom]

-- Retain the native degree-zero object throughout the coefficient square.
private lemma point_target_zero_pull {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ.X f).map (targetZeroIso a S t Y).hom ≫
      (residueOrdinaryRestrictedRegularPullIso Λ.X Λ'.X a.hom.hom f).hom =
    (pointComplexComp Λ f ((CochainComplex.singleFunctor _ 0).obj S.X₃)).hom.f 0 ≫
      (targetZeroIso a S t X).hom := by
  have h := point_ordinary_coefficient a f S.X₃
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃).hom ≫ t.hom)
  rw [targetZeroIso_hom_comp, targetZeroIso_hom_comp]
  rw [pointComplexComp_hom_f]
  run_tac withMainContext do
    structuralCast (← getMainGoal) (← getLocalDeclFromUserName `h).toExpr

-- Prove naturality for abstract complexes before inserting the mapping-cone augmentation.
private lemma pointComplexComp_naturality (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) {C D : CochainComplex (PointModules Λ) ℤ}
    (g : C ⟶ D) :
    ((CondensedRing.upperStar Λ.X f).mapHomologicalComplex (.up ℤ)).map
        (((pointPull Λ Y).mapHomologicalComplex (.up ℤ)).map g) ≫
      (pointComplexComp Λ f D).hom =
    (pointComplexComp Λ f C).hom ≫
      ((pointPull Λ X).mapHomologicalComplex (.up ℤ)).map g := by
  have h := (Functor.mapHomologicalComplexCompIso (pointModuleComp Λ f) (.up ℤ)).hom.naturality g
  dsimp only [pointComplexComp, Iso.app_hom, Functor.comp_map, Functor.comp_obj] at h ⊢
  run_tac withMainContext do
    structuralCast (← getMainGoal) (← getLocalDeclFromUserName `h).toExpr

-- The ordinary square on complexes is determined by its degree-zero coefficient summand.
private lemma total_tensor_pull {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Y) ℤ) :
    let F := CondensedRing.upperStar Λ.X f
    let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
    let EC := ((Mod.extendScalars (betaMap a Y)).mapHomologicalComplex (.up ℤ)).obj C
    let p := (NatTrans.mapHomologicalComplex
      (pullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app C
    let q := (NatTrans.mapHomologicalComplex
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app EC
    (F.mapHomologicalComplex (.up ℤ)).map ((betaTotalNatIso a S t Y).hom.app C) ≫
      q ≫ ((Mod.comap (betaMap a X)).mapHomologicalComplex (.up ℤ)).map p =
    ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app
        (target Λ S Y)).app C ≫
      HomologicalComplex.tensorHom
        (pointComplexComp Λ f ((CochainComplex.singleFunctor _ 0).obj S.X₃)).hom (𝟙 FC) ≫
      (betaTotalNatIso a S t X).hom.app FC := by
  dsimp only
  let F := CondensedRing.upperStar Λ.X f
  let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
  apply finiteFreeScalar_totalPullbackSquare F (target Λ S Y) C _ (target Λ S X) _
    ((betaTotalNatIso a S t Y).app C) ((betaTotalNatIso a S t X).hom.app FC)
    (pointComplexComp Λ f ((CochainComplex.singleFunctor _ 0).obj S.X₃)).hom _
    (betaCoefficient a Y) (betaCoefficient a X)
    (targetZeroIso a S t Y).hom (targetZeroIso a S t X).hom
    (residueOrdinaryRestrictedRegularPullIso Λ.X Λ'.X a.hom.hom f).hom
    (fun n ↦ (betaOrdinary a Y).hom.app (C.X n))
    (fun n ↦ (betaOrdinary a X).hom.app (F.obj (C.X n)))
  · intro n
    simpa only [tensorHom_id, Iso.app_hom] using betaTotalIso_summand a S t Y C n
  · intro n
    simpa only [FC, Functor.mapHomologicalComplex_obj_X, tensorHom_id, Iso.app_hom] using
      betaTotalIso_summand a S t X FC n
  · intro n
    exact ordinary_tensor_pull a f (C.X n)
  · exact point_target_zero_pull a S t f

-- Check naturality degreewise using the explicit point-comparison component.
private lemma point_augmentation_pull (Λ : ScalarSixRing.{u})
    (S : ShortComplex (PointModules Λ)) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((CondensedRing.upperStar Λ.X f).mapHomologicalComplex (.up ℤ)).map
        (augmentation Λ S Y) ≫
      (pointComplexComp Λ f ((CochainComplex.singleFunctor _ 0).obj S.X₃)).hom =
    (pointComplexComp Λ f (CochainComplex.monoCokernelComplex S.f)).hom ≫
      augmentation Λ S X := by
  simpa only [augmentation] using
    pointComplexComp_naturality Λ f (CochainComplex.monoCokernelAugmentation S)

private lemma complexTensorNaturality
    {A B : Type*} [Category.{u + 1} A] [Category.{u + 1} B]
    [Abelian A] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} A] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [MonoidalClosed A] [MonoidalClosed B] [BraidedCategory A] [BraidedCategory B]
    (F : A ⥤ B) [F.Additive] [F.IsLeftAdjoint] [F.OplaxMonoidal]
    {P T : CochainComplex A ℤ} (a : P ⟶ T) (C : CochainComplex A ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (a ⊗ₘ 𝟙 C) ≫
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app T).app C =
    ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app C ≫
      ((F.mapHomologicalComplex (.up ℤ)).map a ⊗ₘ 𝟙 _) := by
  have h := HomologicalComplex.mapBifunctorComparison_naturality
    (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) a (𝟙 C)
  rw [(F.mapHomologicalComplex (.up ℤ)).map_id] at h
  simp only [tensorHom_id]
  change (F.mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.tensorHom a (𝟙 C)) ≫
      HomologicalComplex.mapBifunctorComparison
        (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) T C =
    HomologicalComplex.mapBifunctorComparison
        (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) P C ≫
      HomologicalComplex.tensorHom ((F.mapHomologicalComplex (.up ℤ)).map a) (𝟙 _)
  exact h

private lemma augmentTensorSquare
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    (F : A ⥤ B) (P T C U : A) (PX TX V : B)
    (a : P ⟶ T) (p : F.obj P ⟶ PX) (t : F.obj T ⟶ TX) (aX : PX ⟶ TX)
    (τ : T ⊗ C ⟶ U) (τX : TX ⊗ F.obj C ⟶ V) (q : F.obj U ⟶ V)
    (sP : F.obj (P ⊗ C) ⟶ F.obj P ⊗ F.obj C)
    (sT : F.obj (T ⊗ C) ⟶ F.obj T ⊗ F.obj C)
    (h : F.map τ ≫ q = sT ≫ (t ⊗ₘ 𝟙 _) ≫ τX)
    (hn : F.map (a ⊗ₘ 𝟙 C) ≫ sT = sP ≫ (F.map a ⊗ₘ 𝟙 _))
    (ha : F.map a ≫ t = p ≫ aX) :
    F.map ((a ⊗ₘ 𝟙 C) ≫ τ) ≫ q =
      sP ≫ (p ⊗ₘ 𝟙 _) ≫ (aX ⊗ₘ 𝟙 _) ≫ τX := by
  rw [Functor.map_comp, Category.assoc, h, ← Category.assoc, hn]
  simp only [Category.assoc]
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, ha]

-- Insert the natural augmentation into the ordinary total-tensor square.
private lemma augmented_tensor_pull {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Y) ℤ) :
    let F := CondensedRing.upperStar Λ.X f
    let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
    let EC := ((Mod.extendScalars (betaMap a Y)).mapHomologicalComplex (.up ℤ)).obj C
    let p := (NatTrans.mapHomologicalComplex
      (pullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app C
    let q := (NatTrans.mapHomologicalComplex
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app EC
    (F.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.tensorHom (augmentation Λ S Y) (𝟙 C) ≫
          (betaTotalNatIso a S t Y).hom.app C) ≫
      q ≫ ((Mod.comap (betaMap a X)).mapHomologicalComplex (.up ℤ)).map p =
    ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app
        (complex Λ S Y)).app C ≫
      HomologicalComplex.tensorHom
        (pointComplexComp Λ f (CochainComplex.monoCokernelComplex S.f)).hom (𝟙 FC) ≫
      HomologicalComplex.tensorHom (augmentation Λ S X) (𝟙 FC) ≫
      (betaTotalNatIso a S t X).hom.app FC := by
  dsimp only
  let F := CondensedRing.upperStar Λ.X f
  let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
  apply augmentTensorSquare (F.mapHomologicalComplex (.up ℤ))
    (complex Λ S Y) (target Λ S Y) C _ (complex Λ S X) (target Λ S X) _
    (augmentation Λ S Y)
    (pointComplexComp Λ f (CochainComplex.monoCokernelComplex S.f)).hom
    (pointComplexComp Λ f ((CochainComplex.singleFunctor _ 0).obj S.X₃)).hom
    (augmentation Λ S X)
    ((betaTotalNatIso a S t Y).hom.app C) ((betaTotalNatIso a S t X).hom.app FC) _
    (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app
      (complex Λ S Y)).app C)
    (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app
      (target Λ S Y)).app C)
  · exact total_tensor_pull a S t f C
  · exact complexTensorNaturality F (augmentation Λ S Y) C
  · exact point_augmentation_pull Λ S f

-- Compute the scalar mate before using any K-flat invertibility.
private lemma restricted_scalar_pull_computes
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Y) ℤ) :
    let F := CondensedRing.upperStar Λ.X f
    let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
    let EC := ((Mod.extendScalars (betaMap a Y)).mapHomologicalComplex (.up ℤ)).obj C
    let p := (NatTrans.mapHomologicalComplex
      (pullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app C
    let q := (NatTrans.mapHomologicalComplex
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app EC
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
        ((scalarSixChange a Y).obj (DerivedCategory.Q.obj C)) ≫
      (restriction a X).map ((D.theta a f).inv.app (DerivedCategory.Q.obj C)) ≫
      (restriction a X).map
        ((scalarSixChange a X).map (F.mapDerivedCategoryFactors.hom.app C)) ≫
      (betaRestrictedCounit a X).app FC =
    (scalarSixPull Λ f).map ((betaRestrictedCounit a Y).app C) ≫
      F.mapDerivedCategoryFactors.hom.app
        (((Mod.comap (betaMap a Y)).mapHomologicalComplex (.up ℤ)).obj EC) ≫
      DerivedCategory.Q.map q ≫
      DerivedCategory.Q.map
        (((Mod.comap (betaMap a X)).mapHomologicalComplex (.up ℤ)).map p) := by
  simpa only [betaRestrictedCounit, betaScalarCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, betaMap] using
    finiteFreeScalar_restrictedCounit_pullback D a f C

-- Transport a commuting square through a natural comparison before substituting
-- the concrete complexes, whose two presentations have expensive conversions.
private lemma factors_naturality_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Q : A ⥤ C) (R : B ⥤ D) (F : A ⥤ B) (G : C ⥤ D)
    (η : Q ⋙ G ⟶ F ⋙ R) {P E : A} {T : B}
    (w : P ⟶ E) (q : F.obj E ⟶ T) (e : F.obj P ⟶ T)
    (h : F.map w ≫ q = e) :
    G.map (Q.map w) ≫ η.app E ≫ R.map q = η.app P ≫ R.map e := by
  have hn := η.naturality w
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← R.map_comp, h]

private lemma normalized_pullback_paste
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Q : A ⥤ C) (R : B ⥤ D) (F : A ⥤ B) (G : C ⥤ D)
    (η : Q ⋙ G ⟶ F ⋙ R) {P E : A} {T : B} {U V : C}
    (b : V ⟶ U) (r : U ⟶ Q.obj E) (k : G.obj U ⟶ R.obj T)
    (m : V ⟶ Q.obj P) (w : P ⟶ E) (q : F.obj E ⟶ T) (e : F.obj P ⟶ T)
    (hb : b ≫ r = m ≫ Q.map w)
    (hr : k = G.map r ≫ η.app E ≫ R.map q) (hw : F.map w ≫ q = e) :
    G.map b ≫ k = G.map m ≫ η.app P ≫ R.map e := by
  rw [hr, ← G.map_comp_assoc, hb, G.map_comp, Category.assoc,
    factors_naturality_square Q R F G η w q e hw]

private lemma coherence
    {A B : Type*} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B]
    (Q : A ⥤ B) [Q.LaxMonoidal]
    {P PX C : A} {U V : B}
    (a : U ⟶ Q.obj P) (b : V ⟶ Q.obj C) (p : P ⟶ PX) :
    (((a ≫ Q.map p) ⊗ₘ 𝟙 V) ≫
        (𝟙 (Q.obj PX) ⊗ₘ b) ≫ Functor.LaxMonoidal.μ Q PX C) =
      (a ⊗ₘ b) ≫ Functor.LaxMonoidal.μ Q P C ≫ Q.map (p ⊗ₘ 𝟙 C) := by
  calc
    _ = (a ⊗ₘ b) ≫ (Q.map p ⊗ₘ 𝟙 (Q.obj C)) ≫
        Functor.LaxMonoidal.μ Q PX C := by
      simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
    _ = _ := by
      simp only [tensorHom_id]
      rw [Functor.LaxMonoidal.μ_natural_left]

-- Compute the localized ordinary square independently of the final counit cancellation.
private lemma normalized_beta_pullback_computes
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (β : tensorLeft (DerivedCategory.Q.obj (complex Λ S Y)) ≅
      scalarSixChange a Y ⋙ restriction a Y)
    (hβ : AugmentationNormalized a S t Y β)
    (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Y) ℤ)
    (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) :
    let F := CondensedRing.upperStar Λ.X f
    let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
    let c := F.mapDerivedCategoryFactors.hom.app C
    (scalarSixPull Λ f).map (β.hom.app (DerivedCategory.Q.obj C)) ≫
      (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
        ((scalarSixChange a Y).obj (DerivedCategory.Q.obj C)) ≫
      (restriction a X).map ((D.theta a f).inv.app (DerivedCategory.Q.obj C)) ≫
      (restriction a X).map ((scalarSixChange a X).map c) ≫
      (betaRestrictedCounit a X).app FC =
    (scalarSixPull Λ f).map
        (Functor.LaxMonoidal.μ DerivedCategory.Q (complex Λ S Y) C) ≫
      F.mapDerivedCategoryFactors.hom.app (complex Λ S Y ⊗ C) ≫
      DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app
          (complex Λ S Y)).app C) ≫
      DerivedCategory.Q.map (HomologicalComplex.tensorHom
        (pointComplexComp Λ f (CochainComplex.monoCokernelComplex S.f)).hom (𝟙 FC)) ≫
      DerivedCategory.Q.map (HomologicalComplex.tensorHom (augmentation Λ S X) (𝟙 FC)) ≫
      DerivedCategory.Q.map ((betaTotalNatIso a S t X).hom.app FC) := by
  dsimp only
  let F := CondensedRing.upperStar Λ.X f
  let wY : complex Λ S Y ⊗ C ⟶
      ((Mod.comap (betaMap a Y)).mapHomologicalComplex (.up ℤ)).obj
        (((Mod.extendScalars (betaMap a Y)).mapHomologicalComplex (.up ℤ)).obj C) :=
    HomologicalComplex.tensorHom (augmentation Λ S Y) (𝟙 C) ≫
      (betaTotalNatIso a S t Y).hom.app C
  have hNY : β.hom.app (DerivedCategory.Q.obj C) ≫
      (betaRestrictedCounit a Y).app C =
    Functor.LaxMonoidal.μ DerivedCategory.Q (complex Λ S Y) C ≫
      DerivedCategory.Q.map wY := by
    rw [DerivedCategory.Q.map_comp]
    exact normalized_beta_computes a S t Y β hβ C hC
  have hr := restricted_scalar_pull_computes D a f C
  have hOrd := augmented_tensor_pull a S t f C
  have h := normalized_pullback_paste DerivedCategory.Q DerivedCategory.Q
    (F.mapHomologicalComplex (.up ℤ)) F.mapDerivedCategory
    F.mapDerivedCategoryFactors.hom
    (β.hom.app (DerivedCategory.Q.obj C)) ((betaRestrictedCounit a Y).app C) _
    (Functor.LaxMonoidal.μ DerivedCategory.Q (complex Λ S Y) C) wY _ _ hNY
    (by simpa only [Functor.map_comp, Category.assoc, scalarSixPull, F] using hr) hOrd
  simpa only [Functor.map_comp, Category.assoc, scalarSixPull, F] using h

-- The composition compares exact and total derived realizations of the same complexes.
/--
For a K-flat representative, transport the representative comparison
through exact point pullback. The normalized augmentation equation identifies the
scalar-first map with the tensor pullback comparison; the K-flat counits are
isomorphisms, so cancellation gives the displayed equation.
-/
theorem finiteFreeScalarDerivedComparison_beta_pullback_kflat
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (β : ∀ Z : Scheme.{u}, tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
      scalarSixChange a Z ⋙ restriction a Z)
    (hβ : ∀ Z, AugmentationNormalized a S t Z (β Z))
    (X Y : Scheme.{u}) (f : X ⟶ Y)
    (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Y) ℤ)
    (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) :
    (scalarSixPull Λ f).map ((β Y).hom.app (DerivedCategory.Q.obj C)) ≫
        (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
          ((scalarSixChange a Y).obj (DerivedCategory.Q.obj C)) ≫
        (restriction a X).map ((D.theta a f).inv.app (DerivedCategory.Q.obj C)) =
      tensorPull Λ f (DerivedCategory.Q.obj (complex Λ S Y)) (DerivedCategory.Q.obj C) ≫
        ((modelPull Λ S f).hom ⊗ₘ 𝟙 ((scalarSixPull Λ f).obj (DerivedCategory.Q.obj C))) ≫
        (β X).hom.app ((scalarSixPull Λ f).obj (DerivedCategory.Q.obj C)) := by
  dsimp only [scalarSixPull]
  let F := CondensedRing.upperStar Λ.X f
  let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
  let c := F.mapDerivedCategoryFactors.hom.app C
  have hFC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat FC :=
    CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj Λ.X f hC
  have hNX := normalized_beta_computes a S t X (β X) (hβ X) FC hFC
  have hc : IsIso c := inferInstance
  have hrc : IsIso ((betaRestrictedCounit a X).app FC) := by
    have : IsIso ((betaScalarCounit a X).app FC) := by
      simpa only [betaScalarCounit] using betaScalarCounit_isIso a X FC hFC
    simpa only [betaRestrictedCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] using
      (inferInstance : IsIso ((restriction a X).map ((betaScalarCounit a X).app FC) ≫
        (Mod.comap (betaMap a X)).mapDerivedCategoryFactors.hom.app
          (((Mod.extendScalars (betaMap a X)).mapHomologicalComplex (.up ℤ)).obj FC)))
  apply (cancel_mono
    ((restriction a X).map ((scalarSixChange a X).map c) ≫
      (betaRestrictedCounit a X).app FC)).1
  simp only [Category.assoc]
  have hleft := normalized_beta_pullback_computes D a S t f (β Y) (hβ Y) C hC
  have hn : (β X).hom.app ((scalarSixPull Λ f).obj (DerivedCategory.Q.obj C)) ≫
      (restriction a X).map ((scalarSixChange a X).map c) =
    (𝟙 (DerivedCategory.Q.obj (complex Λ S X)) ⊗ₘ c) ≫
      (β X).hom.app (DerivedCategory.Q.obj FC) := by
    simpa only [Functor.comp_map, tensorLeft, curriedTensor_obj_map, ← id_tensorHom,
      scalarSixPull, F, FC, Functor.comp_obj] using ((β X).hom.naturality c).symm
  have hn' := congrArg (fun k ↦ k ≫ (betaRestrictedCounit a X).app FC) hn
  have hnX := congrArg
    (fun k ↦ (𝟙 (DerivedCategory.Q.obj (complex Λ S X)) ⊗ₘ c) ≫ k) hNX
  simp only [Category.assoc] at hn' hnX
  have hright := congrArg
    (fun k ↦ tensorPull Λ f (DerivedCategory.Q.obj (complex Λ S Y))
      (DerivedCategory.Q.obj C) ≫
      ((modelPull Λ S f).hom ⊗ₘ
        𝟙 ((scalarSixPull Λ f).obj (DerivedCategory.Q.obj C))) ≫ k) (hn'.trans hnX)
  have hh := congrArg
    (fun k ↦ tensorPull Λ f (DerivedCategory.Q.obj (complex Λ S Y))
      (DerivedCategory.Q.obj C) ≫ k)
    (coherence DerivedCategory.Q (F.mapDerivedCategoryFactors.hom.app (complex Λ S Y)) c
      (pointComplexComp Λ f (CochainComplex.monoCokernelComplex S.f)).hom)
  have ht := congrArg
    (fun k ↦ k ≫ DerivedCategory.Q.map (HomologicalComplex.tensorHom
      (pointComplexComp Λ f (CochainComplex.monoCokernelComplex S.f)).hom (𝟙 FC)))
    (finiteFreeScalar_tensorPull_computes Λ f (complex Λ S Y) C)
  simp only [Category.assoc] at hh ht
  have hhead := hh.trans ht
  have htail := congrArg (fun k ↦ k ≫
    DerivedCategory.Q.map (HomologicalComplex.tensorHom (augmentation Λ S X) (𝟙 FC)) ≫
    DerivedCategory.Q.map ((betaTotalNatIso a S t X).hom.app FC)) hhead
  simp only [Category.assoc] at htail
  have hright' := hright.trans htail
  simpa only [modelPull, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    scalarSixPull, F] using hleft.trans hright'.symm

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
