/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientAugmentation
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ExactRealizationTargetZero
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.CanonicalFinitePadicRestriction
import Mathlib.Lean.Meta.CongrTheorems
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.RootEndpointTranspose.ShiftHelpers.DiagonalRootEndpointTransposeCore
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The degree-zero cyclic augmentation endpoint -/

/- Repair note: this proved helper is delivered together with its DAG node. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Mod.derivedExtendMapDerivedCategoryAdjunction
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions

attribute [local semireducible] cyclicCompletedQuotient cyclicDiscreteRestriction
  UniformizerSquareData.scalarAdjunction

-- Expose object aliases to implicit checks without changing instance indexing.
attribute [local implicit_reducible] Mod.forget Mod.comap
  Scheme.purTwistZlOne Scheme.proEtaleRootsOfUnityTower Functor.ofOpSequence
  Functor.ofSequence
  cyclicCompletedQuotient
attribute [local instance_reducible] cyclicDiscreteRestriction cyclicFiniteEvaluationFunctor
  cyclicEvaluationFunctor UniformizerSquareData.scalarAdjunction



-- Keep the specified endpoint objects and exact functors as named data.
attribute [local irreducible] cyclicLine cyclicLineMap geoCartierLine
  Scheme.purTwistZlModule diagonalForget diagonalFiniteToPadic derivedScalars

-- Build explicit congruence proofs at derived-functor conversion boundaries.
-- The kernel checks every generated equality; leaves use only definitional equality.
open Lean Meta in
private meta def structuralProof (a b : Expr) : Nat → MetaM Expr
  | 0 => do
    unless ← isDefEq a b do throwError "nonconvertible leaf"
    mkHEqRefl a
  | fuel + 1 => do
    let a := (← instantiateMVars a).cleanupAnnotations
    let b := (← instantiateMVars b).cleanupAnnotations
    if a == b then return ← mkHEqRefl a
    let f := a.getAppFn
    if f.isConst && f == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs &&
        a.getAppNumArgs > 0 &&
        !([``Functor.mapDerivedCategory, ``DerivedCategory.singleFunctor,
          ``Functor.mapDerivedCategorySingleFunctor].contains f.constName!) then
      try
        let c ← mkHCongrWithArity f a.getAppNumArgs
        let mut proof := c.proof
        for ((x, y), kind) in (a.getAppArgs.zip b.getAppArgs).zip c.argKinds do
          match kind with
          | .eq =>
            proof := mkAppN proof #[x, y, ← mkEqOfHEq (← structuralProof x y fuel)]
          | .heq =>
            proof := mkAppN proof #[x, y, ← structuralProof x y fuel]
          | .fixed => proof := mkApp proof x
          | _ => throwError "unexpected congruence argument"
        if (← inferType proof).isHEq then return proof
        return ← mkHEqOfEq proof
      catch _ => pure ()
    unless ← isDefEq a b do throwError "nonconvertible terms"
    mkHEqRefl a

-- Transport proposition arguments explicitly instead of asking the kernel to
-- compare two fully expanded component maps of the same derived functor.
open Lean Meta Elab Tactic in
private meta def structuralExact (t : Syntax) : TacticM Unit := withMainContext do
  let t ← t.replaceM fun stx => do
    match stx with
    | .ident info raw name pre =>
      pure (some (.ident info raw name.eraseMacroScopes pre))
    | _ => pure none
  let full ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let full ← instantiateMVars full
  if full.hasExprMVar then throwError "unresolved metavariables"
  let mut app := full.getAppFn
  for arg in full.getAppArgs do
    let fnType ← whnf (← inferType app)
    let .forallE _ expectedType _ _ := fnType | throwError "not a function"
    let actualType ← inferType arg
    let mut arg := arg
    if actualType != expectedType && (← isProp expectedType) then
      let h ← mkEqOfHEq (← structuralProof (← whnf actualType) (← whnf expectedType) 12)
      arg ← mkAppM ``Eq.mp #[h, arg]
    app := mkApp app arg
  let goal ← getMainGoal
  let target ← whnf (← goal.getType)
  let actualType ← whnf (← inferType app)
  if actualType != target then
    let h ← mkEqOfHEq (← structuralProof actualType target 12)
    app ← mkAppM ``Eq.mp #[h, app]
  goal.assign app
  replaceMainGoal []

private def single_augmentation_equation
    {B C F : Type*} [Category B] [Category C] [Category F]
    [Abelian B] [Abelian C] [Abelian F]
    [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory F]
    (W : B ⥤ F) (V : C ⥤ F)
    [W.Additive] [V.Additive]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (T : DerivedCategory B ⥤ DerivedCategory C)
    (η : W.mapDerivedCategory ⟶ T ⋙ V.mapDerivedCategory)
    {L : B} {N : C}
    (j : T.obj ((DerivedCategory.singleFunctor B 0).obj L) ⟶
      (DerivedCategory.singleFunctor C 0).obj N)
    (h : W.obj L ⟶ V.obj N) : Prop :=
  η.app ((DerivedCategory.singleFunctor B 0).obj L) ≫
      V.mapDerivedCategory.map j ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app N =
    (W.mapDerivedCategorySingleFunctor 0).hom.app L ≫
      (DerivedCategory.singleFunctor F 0).map h

private theorem exact_scalar_unit
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (R : B ⥤ A) (U : A ⥤ C) [R.Additive] [U.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (L : DerivedCategory A ⥤ DerivedCategory B) (adj : L ⊣ R.mapDerivedCategory)
    (M : A) (N : B) (d : L.obj ((DerivedCategory.singleFunctor A 0).obj M) ⟶
      (DerivedCategory.singleFunctor B 0).obj N) (m : M ⟶ R.obj N)
    (h0 : U.obj M ⟶ U.obj (R.obj N)) (hm : U.map m = h0)
    (hd : adj.homEquiv _ _ d =
      (DerivedCategory.singleFunctor A 0).map m ≫
        (R.mapDerivedCategorySingleFunctor 0).inv.app N) :
    single_augmentation_equation U (R ⋙ U) L
      (Functor.whiskerRight adj.unit U.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L
          ((Functor.mapDerivedCategoryCompIso R U) ≪≫
            Iso.refl (R ⋙ U).mapDerivedCategory).hom) d h0 := by
  dsimp only [single_augmentation_equation]
  rw [← hm]
  rw [Adjunction.homEquiv_unit] at hd
  have hn := (Functor.mapDerivedCategoryCompIso R U).hom.naturality d
  dsimp only [Functor.comp_map] at hn
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom,
    NatTrans.id_app]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [← reassoc_of% hn, ← U.mapDerivedCategory.map_comp_assoc, hd]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor R U N]
  simp only [Iso.hom_inv_id_app_assoc, ← U.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  exact (congrArg (fun f ↦ U.mapDerivedCategory.map f ≫
      (U.mapDerivedCategorySingleFunctor 0).hom.app (R.obj N))
        (Category.comp_id ((DerivedCategory.singleFunctor A 0).map m))).trans
    ((U.mapDerivedCategorySingleFunctor 0).hom.naturality m)

private def scalar_endpoint_equation
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb X)]
    {M : Modules Λ X} {N : Modules Λ' X}
    (j : (derivedScalars a X).obj
        ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟶
      (DerivedCategory.singleFunctor (Modules Λ' X) 0).obj N)
    (h : M.X ⟶ N.X) : Prop :=
  let B := Mod (DiagonalAb X) (condensedRingObj Λ X)
  let C := Mod (DiagonalAb X) (condensedRingObj Λ' X)
  let W : B ⥤ DiagonalAb X := Mod.forget _
  let V : C ⥤ DiagonalAb X := Mod.forget _
  let T : DerivedCategory B ⥤ DerivedCategory C := derivedScalars a X
  let η : W.mapDerivedCategory ⟶ T ⋙ V.mapDerivedCategory := scalarUnderlyingUnit a X
  single_augmentation_equation W V T η j h


private theorem scalar_unit_endpoint
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb X)]
    {M : Modules Λ X} {N : Modules Λ' X} {m : M.X ⟶ N.X}
    (d : Endpoint a M N m) :
    scalar_endpoint_equation a X d.iso.hom m := by
  dsimp only [scalar_endpoint_equation]
  let R := Mod.comap (D := DiagonalAb X) (coefficientMap a X)
  let U := Mod.forget (D := DiagonalAb X) (condensedRingObj Λ X)
  let V := Mod.forget (D := DiagonalAb X) (condensedRingObj Λ' X)
  let L := derivedScalars a X
  let adj := UniformizerSquareData.scalarAdjunction a X
  have hd := RootEndpointTranspose.ShiftHelpers.scalarEndpoint_transpose a d
  exact exact_scalar_unit R U L adj M N d.iso.hom d.semilinear.hom
    m d.semilinear.underlying hd


private theorem exact_underlying_single
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (E : A ⥤ B) (U : B ⥤ C) (V : A ⥤ C)
    [E.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e : E ⋙ U ≅ V) (M : A) {N : B} (i : E.obj M ⟶ N) :
    ((Functor.mapDerivedCategoryCompIso E U) ≪≫
      Functor.mapDerivedCategoryNatIso e).inv.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      U.mapDerivedCategory.map ((E.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (U.mapDerivedCategorySingleFunctor 0).hom.app (E.obj M) ≫
      (DerivedCategory.singleFunctor C 0).map (U.map i) =
    (V.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor C 0).map (e.inv.app M ≫ U.map i) := by
  simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor E U M]
  rw [← Functor.mapDerivedCategoryNatIso_symm]
  rw [reassoc_of% Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor e.symm M]
  rw [← Functor.map_comp]
  rfl

private theorem two_exact_underlying_single
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : A ⥤ B) (F : B ⥤ C) (U : C ⥤ D) (V : A ⥤ D)
    [E.Additive] [F.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e : E ⋙ F ⋙ U ≅ V) (M : A) {N : B} (i : E.obj M ⟶ N) :
    (Functor.isoWhiskerLeft E.mapDerivedCategory
        (Functor.mapDerivedCategoryCompIso F U) ≪≫
      (Functor.mapDerivedCategoryCompIso E (F ⋙ U)) ≪≫
      Functor.mapDerivedCategoryNatIso e).inv.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      U.mapDerivedCategory.map
        (F.mapDerivedCategory.map
          ((E.mapDerivedCategorySingleFunctor 0).hom.app M ≫
            (DerivedCategory.singleFunctor B 0).map i) ≫
          (F.mapDerivedCategorySingleFunctor 0).hom.app N) ≫
      (U.mapDerivedCategorySingleFunctor 0).hom.app (F.obj N) =
    (V.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor D 0).map (e.inv.app M ≫ U.map (F.map i)) := by
  have hi : F.mapDerivedCategory.map
      ((E.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor B 0).map i) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app N =
    F.mapDerivedCategory.map ((E.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app (E.obj M) ≫
      (DerivedCategory.singleFunctor C 0).map (F.map i) := by
    rw [Functor.map_comp, Category.assoc]
    exact congrArg
      (F.mapDerivedCategory.map ((E.mapDerivedCategorySingleFunctor 0).hom.app M) ≫ ·)
      ((F.mapDerivedCategorySingleFunctor 0).hom.naturality i)
  rw [hi]
  simp only [Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  have hu := (U.mapDerivedCategorySingleFunctor 0).hom.naturality (F.map i)
  dsimp only [Functor.comp_map] at hu
  rw [hu]
  have hc := (Functor.mapDerivedCategoryCompIso F U).inv.naturality
    ((E.mapDerivedCategorySingleFunctor 0).hom.app M)
  dsimp only [Functor.comp_map] at hc
  rw [← reassoc_of% hc]
  rw [reassoc_of% Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor F U (E.obj M)]
  simpa only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.comp_map,
    Functor.map_comp, Category.assoc] using
    exact_underlying_single E (F ⋙ U) V e M i

private theorem exact_square_single
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : A ⥤ B) (Z : A ⥤ C) (U : C ⥤ D) (V : B ⥤ D)
    [E.Additive] [Z.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits Z] [PreservesFiniteColimits Z]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e : Z ⋙ U ≅ E ⋙ V) (M : A) :
    ((Functor.mapDerivedCategoryCompIso Z U) ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso E V).symm).hom.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      V.mapDerivedCategory.map ((E.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app (E.obj M) =
    U.mapDerivedCategory.map ((Z.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (U.mapDerivedCategorySingleFunctor 0).hom.app (Z.obj M) ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app M) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor Z U M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem augmentation_naturality
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (T : A ⥤ B) (G : B ⥤ C) (U : C ⥤ D) (V : B ⥤ D) (W : A ⥤ D)
    (d : G ⋙ U ≅ V) (η : W ⟶ T ⋙ V)
    {M N : A} {P : C} {Q : D} (r : M ⟶ N) (k : G.obj (T.obj N) ⟶ P)
    (c : U.obj P ⟶ Q) :
    η.app M ≫ d.inv.app (T.obj M) ≫ U.map (G.map (T.map r)) ≫ U.map k ≫ c =
      W.map r ≫ η.app N ≫ d.inv.app (T.obj N) ≫ U.map k ≫ c := by
  have hd := d.inv.naturality (T.map r)
  dsimp only [Functor.comp_map] at hd
  rw [← reassoc_of% hd]
  have hη := η.naturality r
  dsimp only [Functor.comp_map] at hη
  rw [← reassoc_of% hη]

private theorem exact_augmentation_target
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory F]
    (Z : A ⥤ E) (J : A ⥤ B) (G : C ⥤ D) (H : D ⥤ E)
    (U : E ⥤ F) (V : C ⥤ F) (W : B ⥤ F)
    [Z.Additive] [J.Additive] [G.Additive] [H.Additive]
    [U.Additive] [V.Additive] [W.Additive]
    [PreservesFiniteLimits Z] [PreservesFiniteColimits Z]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (T : DerivedCategory B ⥤ DerivedCategory C)
    (e : Z ⋙ U ≅ J ⋙ W) (d : G ⋙ H ⋙ U ≅ V)
    (η : W.mapDerivedCategory ⟶ T ⋙ V.mapDerivedCategory)
    (P : A) (L : B) (N : C) (Q : D)
    (i : J.obj P ⟶ L)
    (j : T.obj ((DerivedCategory.singleFunctor B 0).obj L) ⟶
      (DerivedCategory.singleFunctor C 0).obj N)
    (q : G.obj N ⟶ Q) (h : W.obj L ⟶ V.obj N)
    (hj : single_augmentation_equation W V T η j h) :
    let c := (Functor.mapDerivedCategoryCompIso Z U) ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso J W).symm
    let d' := Functor.isoWhiskerLeft G.mapDerivedCategory
        (Functor.mapDerivedCategoryCompIso H U) ≪≫
      (Functor.mapDerivedCategoryCompIso G (H ⋙ U)) ≪≫
      Functor.mapDerivedCategoryNatIso d
    (c.hom.app ((DerivedCategory.singleFunctor A 0).obj P) ≫
      η.app (J.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj P)) ≫
      d'.inv.app (T.obj (J.mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor A 0).obj P)))) ≫
      U.mapDerivedCategory.map (exactRealizationTargetZero J T G H i j q) ≫
      (U.mapDerivedCategorySingleFunctor 0).hom.app (H.obj Q) =
    U.mapDerivedCategory.map ((Z.mapDerivedCategorySingleFunctor 0).hom.app P) ≫
      (U.mapDerivedCategorySingleFunctor 0).hom.app (Z.obj P) ≫
      (DerivedCategory.singleFunctor F 0).map
        (e.hom.app P ≫ W.map i ≫ h ≫ d.inv.app N ≫ U.map (H.map q)) := by
  dsimp only [single_augmentation_equation] at hj
  dsimp only
  simp only [Category.assoc]
  unfold exactRealizationTargetZero
  let d' := Functor.isoWhiskerLeft G.mapDerivedCategory
        (Functor.mapDerivedCategoryCompIso H U) ≪≫
      (Functor.mapDerivedCategoryCompIso G (H ⋙ U)) ≪≫
      Functor.mapDerivedCategoryNatIso d
  let r := (J.mapDerivedCategorySingleFunctor 0).hom.app P ≫
    (DerivedCategory.singleFunctor B 0).map i
  let k := H.mapDerivedCategory.map
      (G.mapDerivedCategory.map j ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
        (DerivedCategory.singleFunctor D 0).map q) ≫
    (H.mapDerivedCategorySingleFunctor 0).hom.app Q
  have hk : d'.inv.app (T.obj ((DerivedCategory.singleFunctor B 0).obj L)) ≫
      U.mapDerivedCategory.map k ≫
      (U.mapDerivedCategorySingleFunctor 0).hom.app (H.obj Q) =
    V.mapDerivedCategory.map j ≫ (V.mapDerivedCategorySingleFunctor 0).hom.app N ≫
      (DerivedCategory.singleFunctor F 0).map (d.inv.app N ≫ U.map (H.map q)) := by
    dsimp only [k]
    simp only [Functor.map_comp, Category.assoc]
    have hd := d'.inv.naturality j
    dsimp only [Functor.comp_map] at hd
    rw [← reassoc_of% hd]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (V.mapDerivedCategory.map j ≫ ·)
        (two_exact_underlying_single G H U V d N q)
  have hη : η.app ((DerivedCategory.singleFunctor B 0).obj L) ≫
      d'.inv.app (T.obj ((DerivedCategory.singleFunctor B 0).obj L)) ≫
      U.mapDerivedCategory.map k ≫
      (U.mapDerivedCategorySingleFunctor 0).hom.app (H.obj Q) =
    (W.mapDerivedCategorySingleFunctor 0).hom.app L ≫
      (DerivedCategory.singleFunctor F 0).map (h ≫ d.inv.app N ≫ U.map (H.map q)) := by
    rw [hk, reassoc_of% hj]
    simp only [Functor.map_comp]
  rw [Functor.map_comp, Category.assoc]
  erw [augmentation_naturality T (G.mapDerivedCategory ⋙ H.mapDerivedCategory)
    U.mapDerivedCategory V.mapDerivedCategory W.mapDerivedCategory d' η r k
    ((U.mapDerivedCategorySingleFunctor 0).hom.app (H.obj Q))]
  rw [hη]
  dsimp only [r]
  simp only [Functor.map_comp, Category.assoc]
  have hw := (W.mapDerivedCategorySingleFunctor 0).hom.naturality i
  dsimp only [Functor.comp_map] at hw
  rw [reassoc_of% hw]
  rw [reassoc_of% exact_square_single J Z U W e P]

private theorem cyclic_augmentation_app
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n)
    (P : DerivedCategory (DiagonalCompleted l (diagonalSurface Y))) :
    (cyclicEvaluationAugmentation l Y n eW p).app P =
      ((Functor.mapDerivedCategoryCompIso
          (diagonalCompletedRestriction l (diagonalSurface Y))
          (diagonalForget l (diagonalSurface Y))) ≪≫
        Functor.mapDerivedCategoryNatIso eW.underlying.symm ≪≫
        (Functor.mapDerivedCategoryCompIso eW.F
          (Mod.forget (D := DiagonalAb (diagonalSurface Y))
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l])
            (diagonalSurface Y)))).symm).hom.app P ≫
      (scalarUnderlyingUnit (cyclicMap l n) (diagonalSurface Y)).app
        (eW.F.mapDerivedCategory.obj P) ≫
      (Functor.isoWhiskerLeft p.eW.F.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso
            (canonicalFinitePadicRestriction l n (diagonalSurface Y))
            (diagonalForget l (diagonalSurface Y))) ≪≫
        (Functor.mapDerivedCategoryCompIso p.eW.F
          (canonicalFinitePadicRestriction l n (diagonalSurface Y) ⋙
            diagonalForget l (diagonalSurface Y))) ≪≫
        Functor.mapDerivedCategoryNatIso (cyclicFiniteUnderlying l Y n p)).inv.app
          ((derivedScalars (cyclicMap l n) (diagonalSurface Y)).obj
            (eW.F.mapDerivedCategory.obj P)) := by
  simp only [cyclicEvaluationAugmentation, cyclicCompletedUnderlying,
    cyclicEvaluationUnderlying, NatTrans.comp_app, Functor.whiskerLeft_app,
    id_eq, Functor.isoWhiskerLeft_inv, Functor.comp_obj]

private theorem cyclic_augmentation_target_for
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n)
    (P : DiagonalCompleted l (diagonalSurface Y))
    (L : Modules (Profinite.continuousMapRingObj ℤ_[l]) (diagonalSurface Y))
    (N : Modules (Profinite.continuousMapRingObj (ZMod (l ^ (n + 1)))) (diagonalSurface Y))
    (Q : Sheaf (Scheme.ProEt.topology (diagonalSurface Y))
      (@ModuleCat.{u + 1} (diagonalResidue.{u} l n)
        (inferInstance : CommRing (diagonalResidue.{u} l n)).toRing))
    (i : eW.F.obj P ⟶ L)
    (j : (derivedScalars (cyclicMap l n) (diagonalSurface Y)).obj
        ((DerivedCategory.singleFunctor _ 0).obj L) ⟶
      (DerivedCategory.singleFunctor _ 0).obj N)
    (q : p.eW.F.obj N ⟶ Q) (h : L.X ⟶ N.X)
    (hj : scalar_endpoint_equation (cyclicMap l n) (diagonalSurface Y) j h) :
    (cyclicEvaluationAugmentation l Y n eW p).app
        ((DerivedCategory.singleFunctor _ 0).obj P) ≫
      (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map
        (exactRealizationTargetZero eW.F
          (derivedScalars (cyclicMap l n) (diagonalSurface Y)) p.eW.F
          (canonicalFinitePadicRestriction l n (diagonalSurface Y)) i j q) ≫
      ((diagonalForget l (diagonalSurface Y)).mapDerivedCategorySingleFunctor 0).hom.app _ =
    (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map
        (((diagonalCompletedRestriction l (diagonalSurface Y)).mapDerivedCategorySingleFunctor
          0).hom.app P) ≫
      ((diagonalForget l (diagonalSurface Y)).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor _ 0).map
        (eW.underlying.inv.app P ≫ i.hom ≫ h ≫
          (cyclicFiniteUnderlying l Y n p).inv.app N ≫
          (diagonalForget l (diagonalSurface Y)).map
            ((canonicalFinitePadicRestriction l n (diagonalSurface Y)).map q)) := by
  dsimp only [scalar_endpoint_equation] at hj
  have hh := exact_augmentation_target
    (diagonalCompletedRestriction l (diagonalSurface Y)) eW.F p.eW.F
    (canonicalFinitePadicRestriction l n (diagonalSurface Y))
    (diagonalForget l (diagonalSurface Y))
    (Mod.forget (D := DiagonalAb (diagonalSurface Y)) (condensedRingObj
      (Profinite.continuousMapRingObj (ZMod (l ^ (n + 1)))) (diagonalSurface Y)))
    (Mod.forget (D := DiagonalAb (diagonalSurface Y))
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) (diagonalSurface Y)))
    (derivedScalars (cyclicMap l n) (diagonalSurface Y)) eW.underlying.symm
    (cyclicFiniteUnderlying l Y n p) (scalarUnderlyingUnit (cyclicMap l n) (diagonalSurface Y))
    P L N Q i j q h hj
  rw [cyclic_augmentation_app]
  exact hh

/-- The unshifted cyclic target, constructed from exact-single comparisons and the
specified completed and finite line endpoints.
Source: coefficient changes (1), root endpoint.
(blueprint: lem-diagonal-cyclic-augmentation-zero). -/
def cyclicEvaluationTargetZero
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    (cyclicEvaluationFunctor l Y n eW p).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.purTwistZlModule (diagonalSurface Y) l)) ⟶
      (DerivedCategory.singleFunctor (DiagonalMod l (diagonalSurface Y)) 0).obj
        ((diagonalFiniteToPadic l n (diagonalSurface Y)).obj
          (geoCartierLine (diagonalResidue l n) (l ^ (n + 1))
            (cartierResidue_cast l (n + 1)) (diagonalSurface Y))) :=
  exactRealizationTargetZero eW.F
    (derivedScalars (cyclicMap l n) (diagonalSurface Y)) p.eW.F
    (canonicalFinitePadicRestriction l n (diagonalSurface Y))
    eW.lineIso.hom p.line.iso.hom p.lineEndpoint.iso.hom

attribute [local irreducible] Functor.mapDerivedCategorySingleFunctor
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors

-- Exact-single coherence involves several derived functor compositions.
/-- The cyclic augmentation followed by the unshifted target has the prescribed
ordinary underlying root arrow.

Source: coefficient changes (1), root endpoint and scalar adjunction.
(blueprint: lem-diagonal-cyclic-augmentation-zero).

Proof: transpose the finite scalar endpoint through its defining derived scalar
adjunction. Compatibility of exact-derived composition and natural isomorphisms
with single objects computes the finite realization factor. Naturality moves the
completed line comparison through the scalar unit and the finite comparison.
The completed realization's underlying comparison on single objects gives the
remaining ordinary completed line arrow. All factors are the specified maps. -/
theorem cyclicEvaluationAugmentation_zeroTarget
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    (cyclicEvaluationAugmentation l Y n eW p).app
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.purTwistZlModule (diagonalSurface Y) l)) ≫
      (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map
        (cyclicEvaluationTargetZero l Y n eW p) ≫
      ((diagonalForget l (diagonalSurface Y)).mapDerivedCategorySingleFunctor 0).hom.app _ =
    (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map
        (((diagonalCompletedRestriction l (diagonalSurface Y)).mapDerivedCategorySingleFunctor
          0).hom.app (Scheme.purTwistZlModule (diagonalSurface Y) l)) ≫
      ((diagonalForget l (diagonalSurface Y)).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor _ 0).map
        (eW.underlying.inv.app (Scheme.purTwistZlModule (diagonalSurface Y) l) ≫
          eW.lineIso.hom.hom ≫ cyclicLineMap l n (diagonalSurface Y) ≫
          (cyclicFiniteUnderlying l Y n p).inv.app (cyclicLine l n (diagonalSurface Y)) ≫
          (diagonalForget l (diagonalSurface Y)).map
            ((diagonalFiniteToPadic l n (diagonalSurface Y)).map
              p.lineEndpoint.iso.hom)) := by
  have hj := scalar_unit_endpoint (cyclicMap l n) (diagonalSurface Y) p.line
  run_tac structuralExact (← `(term| cyclic_augmentation_target_for l Y n eW p
    (Scheme.purTwistZlModule (diagonalSurface Y) l) (zlLine l (diagonalSurface Y))
    (cyclicLine l n (diagonalSurface Y))
    (geoCartierLine (diagonalResidue l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalSurface Y))
    eW.lineIso.hom p.line.iso.hom p.lineEndpoint.iso.hom
    (cyclicLineMap l n (diagonalSurface Y)) hj))

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
