/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.DeligneLaumon.CommonStagePullbackCompData
public import WeilConjectures.DeligneLaumon.CommonStagePullbackCompComponentAux
import WeilConjectures.TraceFormula.Integral.IntegralPullbackCompositionScalarRational
import all Mathlib.Logic.Small.Defs

/-! # Common-stage pullback composition component

(blueprint: lem-zl-common-stage-pullback-comp-naturality). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

attribute [local irreducible] commonStagePullbackCompComponent
  commonStageDerivedPullback constructibleIntegralPullback

-- Use the same cached categories as the existing normalized compositor API.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct GeneralAlgebraicallyClosedCoefficients.stageSystem
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] Functor.category StageSystem.instCategoryPairCategory
  ScalarLocalization.category ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  StageSystem.ι sfRationalConstructibleLocalization ScalarLocalization.localization
  commonStagePullbackObject

set_option allowUnsafeReducibility true in
attribute [local irreducible] ScalarLocalization.composition
  GeneralAlgebraicallyClosedCoefficients.ofHom StageSystem.PairCategory.mkHom
  rationalDerivedPullback commonStagePullbackComparison
  rationalPullbackCompositionIso rationalPullbackScalarComparison
  commonStagePullbackRationalComposition HasDerivedCategory.standard integralCoefficientLinear
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence Scheme.residueField

/-! v4.35 note: the final identification in `commonStagePullbackCompComponent_stage_representation`
goes through a generic transport lemma instantiated in this file (so that every instance term is
the one of this file) and an opaque boundary for the transported comparisons; the single defeq of
the original proof needs about 44 s on v4.35. Statements are unchanged. -/

/-- Generic form of the transport of a compositor square through functors equal to the
scalar extensions. Source: elementary category theory. -/
private theorem compositor_transport
    {AX AY AZ BX BY BZ : Type*} [Category AX] [Category AY] [Category AZ]
    [Category BX] [Category BY] [Category BZ]
    (pEg : AZ ⥤ AY) (pEf : AY ⥤ AX) (pEfg : AZ ⥤ AX)
    (pLg : BZ ⥤ BY) (pLf : BY ⥤ BX) (pLfg : BZ ⥤ BX)
    (SX : AX ⥤ BX) (SY : AY ⥤ BY) (SZ : AZ ⥤ BZ)
    (TX : AX ⥤ BX) (TY : AY ⥤ BY) (TZ : AZ ⥤ BZ)
    (eX : TX = SX) (eY : TY = SY) (eZ : TZ = SZ)
    (ρf : pEf ⋙ SX ≅ SY ⋙ pLf) (ρg : pEg ⋙ SY ≅ SZ ⋙ pLg) (ρfg : pEfg ⋙ SX ≅ SZ ⋙ pLfg)
    (Q : AZ) (wE : pEfg.obj Q ≅ pEf.obj (pEg.obj Q))
    (wL : ∀ Q' : BZ, pLfg.obj Q' ≅ pLf.obj (pLg.obj Q'))
    (R : SX.map wE.hom ≫ ρf.hom.app (pEg.obj Q) ≫ pLf.map (ρg.hom.app Q) =
      ρfg.hom.app Q ≫ (wL (SZ.obj Q)).hom) :
    TX.map wE.hom =
      ((eqToIso eX).app (pEfg.obj Q) ≪≫ ρfg.app Q ≪≫
          pLfg.mapIso ((eqToIso eZ).app Q).symm).hom ≫
        (wL (TZ.obj Q)).hom ≫
        pLf.map ((eqToIso eY).app (pEg.obj Q) ≪≫ ρg.app Q ≪≫
            pLg.mapIso ((eqToIso eZ).app Q).symm).inv ≫
        ((eqToIso eX).app (pEf.obj (pEg.obj Q)) ≪≫ ρf.app (pEg.obj Q) ≪≫
          pLf.mapIso ((eqToIso eY).app (pEg.obj Q)).symm).inv := by
  subst eX eY eZ
  simp only [eqToIso_refl, Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    Iso.refl_hom, Iso.refl_inv, Iso.symm_hom, Iso.symm_inv, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.mapIso_inv, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [Category.id_comp]
  rw [← reassoc_of% R]
  erw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]

/-- A transported comparison whose implementation stays behind an opaque boundary. -/
private irreducible_def commonStageTransportComparison
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (p : A ⥤ B) (q : C ⥤ D)
    (SA TA : A ⥤ C) (SB TB : B ⥤ D) (eA : TA = SA) (eB : TB = SB)
    (ρ : p ⋙ SB ≅ SA ⋙ q) (Q : A) :
    TB.obj (p.obj Q) ≅ q.obj (TA.obj Q) :=
  (eqToIso eB).app (p.obj Q) ≪≫ ρ.app Q ≪≫ q.mapIso ((eqToIso eA).app Q).symm

/-- Transport a compositor using the named comparisons, before specializing the categories. -/
private theorem commonStageTransportCompositor
    {AX AY AZ BX BY BZ : Type*} [Category* AX] [Category* AY] [Category* AZ]
    [Category* BX] [Category* BY] [Category* BZ]
    (pEg : AZ ⥤ AY) (pEf : AY ⥤ AX) (pEfg : AZ ⥤ AX)
    (pLg : BZ ⥤ BY) (pLf : BY ⥤ BX) (pLfg : BZ ⥤ BX)
    (SX TX : AX ⥤ BX) (SY TY : AY ⥤ BY) (SZ TZ : AZ ⥤ BZ)
    (eX : TX = SX) (eY : TY = SY) (eZ : TZ = SZ)
    (ρf : pEf ⋙ SX ≅ SY ⋙ pLf) (ρg : pEg ⋙ SY ≅ SZ ⋙ pLg)
    (ρfg : pEfg ⋙ SX ≅ SZ ⋙ pLfg)
    (Q : AZ) (wE : pEfg.obj Q ≅ pEf.obj (pEg.obj Q))
    (wL : ∀ Q' : BZ, pLfg.obj Q' ≅ pLf.obj (pLg.obj Q'))
    (R : SX.map wE.hom ≫ ρf.hom.app (pEg.obj Q) ≫ pLf.map (ρg.hom.app Q) =
      ρfg.hom.app Q ≫ (wL (SZ.obj Q)).hom) :
    TX.map wE.hom =
      (commonStageTransportComparison pEfg pLfg SZ TZ SX TX eZ eX ρfg Q).hom ≫
        (wL (TZ.obj Q)).hom ≫
        pLf.map (commonStageTransportComparison pEg pLg SZ TZ SY TY eZ eY ρg Q).inv ≫
        (commonStageTransportComparison pEf pLf SY TY SX TX eY eX ρf (pEg.obj Q)).inv := by
  simpa only [commonStageTransportComparison_def] using
    compositor_transport pEg pEf pEfg pLg pLf pLfg SX SY SZ TX TY TZ
      eX eY eZ ρf ρg ρfg Q wE wL R

private theorem normalization_map_heq
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B A' B' : C} (hA : A = A') (hB : B = B')
    {a : A ⟶ B} {b : A' ⟶ B'} (h : HEq a b) : HEq (F.map a) (F.map b) := by
  cases hA
  cases hB
  cases h
  rfl

/-- Cancellation of the inserted comparison isomorphisms in a conjugated square. -/
private theorem stage_square_cancel {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A B A' B' W W' : D} {U U' V V' : C}
    (x : A ⟶ B) (m : B ⟶ B') (y : A' ≅ B') (ρP : B ⟶ G.obj U) (ρQ : B' ⟶ G.obj U')
    (zP : V ≅ U) (zQ : V' ≅ U') (wP : W ≅ G.obj V) (wQ : W' ≅ G.obj V') (n : U ⟶ U')
    (h : ρP ≫ G.map n = m ≫ ρQ) :
    (x ≫ m ≫ y.inv) ≫ (y.hom ≫ ρQ ≫ G.map zQ.inv ≫ wQ.inv) =
      (x ≫ ρP ≫ G.map zP.inv ≫ wP.inv) ≫
        (wP.hom ≫ G.map (zP.hom ≫ n ≫ zQ.inv) ≫ wQ.inv) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp,
    Iso.inv_hom_id_map_assoc, reassoc_of% h]

/-- The conjugated fixed-stage square underlying common-stage naturality.
Source: Stacks 099N(5), finite-stage cancellation after coefficient compatibility.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative).
This is the stage-category equality obtained after inserting the three pullback
comparison isomorphisms; the common-stage wrapper is handled by the parent theorem.
Proof: cancel the inner comparison of `f ≫ g` at `Q` and the comparison of `f` at the
pullback of `P`, expand the pullback of the composite map by functoriality, and apply the
fixed-stage rational naturality. -/
theorem commonStagePullbackCompComponent_stage_square
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    {P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Z}
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
    (r : P.toStage hP ⟶ Q.toStage hQ) :
    ((commonStagePullbackComparison l Ω (f ≫ g) P L hP).hom ≫
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (f ≫ g)).map r ≫
      (commonStagePullbackComparison l Ω (f ≫ g) Q L hQ).inv) ≫
      ((commonStagePullbackComparison l Ω (f ≫ g) Q L hQ).hom ≫
        (commonStagePullbackRationalComposition l Ω f g L Q hQ).hom ≫
        (rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
          ((commonStagePullbackComparison l Ω g Q L hQ).inv) ≫
        (commonStagePullbackComparison l Ω f
          (commonStagePullbackObject l Ω g Q) L hQ).inv) =
      ((commonStagePullbackComparison l Ω (f ≫ g) P L hP).hom ≫
        (commonStagePullbackRationalComposition l Ω f g L P hP).hom ≫
        (rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
          ((commonStagePullbackComparison l Ω g P L hP).inv) ≫
        (commonStagePullbackComparison l Ω f
          (commonStagePullbackObject l Ω g P) L hP).inv) ≫
      ((commonStagePullbackComparison l Ω f
          (commonStagePullbackObject l Ω g P) L hP).hom ≫
        (rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
          ((commonStagePullbackComparison l Ω g P L hP).hom ≫
            (rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).map r ≫
            (commonStagePullbackComparison l Ω g Q L hQ).inv) ≫
        (commonStagePullbackComparison l Ω f
          (commonStagePullbackObject l Ω g Q) L hQ).inv) := by
  exact stage_square_cancel
    (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
    (commonStagePullbackComparison l Ω (f ≫ g) P L hP).hom
    ((rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (f ≫ g)).map r)
    (commonStagePullbackComparison l Ω (f ≫ g) Q L hQ)
    (commonStagePullbackRationalComposition l Ω f g L P hP).hom
    (commonStagePullbackRationalComposition l Ω f g L Q hQ).hom
    (commonStagePullbackComparison l Ω g P L hP)
    (commonStagePullbackComparison l Ω g Q L hQ)
    (commonStagePullbackComparison l Ω f (commonStagePullbackObject l Ω g P) L hP)
    (commonStagePullbackComparison l Ω f (commonStagePullbackObject l Ω g Q) L hQ)
    ((rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).map r)
    (commonStagePullbackRationalComposition_naturality l Ω f g L hP hQ r)

/-- Identify the two presentations of the fixed-stage rational compositor. -/
private theorem commonStagePullbackRationalComposition_eq_scalar
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (hP : P.stage ≤ L) :
    commonStagePullbackRationalComposition l Ω f g L P hP =
      rationalPullbackCompositionIso l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f g
        (P.toStage hP) := by
  unfold commonStagePullbackRationalComposition rationalPullbackCompositionIso
  rfl

/-- Identify one comparison without expanding the surrounding compositor square. -/
private theorem commonStagePullbackComparison_eq_transport
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (hP : P.stage ≤ L)
    (eX : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T hP =
      GeneralAlgebraicallyClosedCoefficients.transition l Ω X P.stage L hP)
    (eY : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T hP =
      GeneralAlgebraicallyClosedCoefficients.transition l Ω Y P.stage L hP) :
    commonStagePullbackComparison l Ω f P L hP =
      commonStageTransportComparison
        (rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f)
        (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
        (GeneralAlgebraicallyClosedCoefficients.transition l Ω Y P.stage L hP)
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T hP)
        (GeneralAlgebraicallyClosedCoefficients.transition l Ω X P.stage L hP)
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T hP) eY eX
        (rationalPullbackScalarComparison l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage L hP) f) P.obj := by
  rw [commonStageTransportComparison_def]
  unfold commonStagePullbackComparison
  rfl

/-- Substitute the three comparisons while keeping the compositor itself opaque. -/
private theorem stage_transport_of_comparisons
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B W : D} {U V : C} (x : A ⟶ W) (b : B ≅ F.obj U)
    {a a' : A ≅ B} {c c' : V ≅ U} {d d' : W ≅ F.obj V}
    (ha : a = a') (hc : c = c') (hd : d = d')
    (h : x = a'.hom ≫ b.hom ≫ F.map c'.inv ≫ d'.inv) :
    x = a.hom ≫ b.hom ≫ F.map c.inv ≫ d.inv := by
  cases ha
  cases hc
  cases hd
  exact h

/-- Transport the rational compositor through the recorded coefficient-stage transitions. -/
private theorem commonStagePullbackCompComponent_stage_transport
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (hP : P.stage ≤ L) :
    (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) P.stage).map
        (rationalPullbackCompositionIso l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f g P.obj).hom =
      (GeneralAlgebraicallyClosedCoefficients.ofHom
        (commonStagePullbackObject l Ω (f ≫ g) P)
        (commonStagePullbackObject l Ω f
          (commonStagePullbackObject l Ω g P)) L hP hP
        ((commonStagePullbackComparison l Ω (f ≫ g) P L hP).hom ≫
          (commonStagePullbackRationalComposition l Ω f g L P hP).hom ≫
          (rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
            ((commonStagePullbackComparison l Ω g P L hP).inv) ≫
          (commonStagePullbackComparison l Ω f
            (commonStagePullbackObject l Ω g P) L hP).inv)) := by
  have eX : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T hP =
      GeneralAlgebraicallyClosedCoefficients.transition l Ω X P.stage L hP := by
    simpa only [GeneralAlgebraicallyClosedCoefficients.stageSystem] using
      (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω X).exists.choose_spec.1
        P.stage L hP
  have eY : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T hP =
      GeneralAlgebraicallyClosedCoefficients.transition l Ω Y P.stage L hP := by
    simpa only [GeneralAlgebraicallyClosedCoefficients.stageSystem] using
      (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω Y).exists.choose_spec.1
        P.stage L hP
  have eZ : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).T hP =
      GeneralAlgebraicallyClosedCoefficients.transition l Ω Z P.stage L hP := by
    simpa only [GeneralAlgebraicallyClosedCoefficients.stageSystem] using
      (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω Z).exists.choose_spec.1
        P.stage L hP
  have key := commonStageTransportCompositor
    (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) g)
    (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f)
    (rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) (f ≫ g))
    (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g)
    (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
    (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (f ≫ g))
    (GeneralAlgebraicallyClosedCoefficients.transition l Ω X P.stage L hP) _
    (GeneralAlgebraicallyClosedCoefficients.transition l Ω Y P.stage L hP) _
    (GeneralAlgebraicallyClosedCoefficients.transition l Ω Z P.stage L hP) _ eX eY eZ
    (rationalPullbackScalarComparison l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage L hP) f)
    (rationalPullbackScalarComparison l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage L hP) g)
    (rationalPullbackScalarComparison l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage L hP) (f ≫ g))
    P.obj (rationalPullbackCompositionIso l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f g P.obj)
    (fun Q ↦ rationalPullbackCompositionIso l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f g Q)
    (rationalPullbackComposition_scalar l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω P.stage L hP) f g P.obj)
  refine (StageSystem.ι_map_eq hP _).trans ?_
  have eR := commonStagePullbackRationalComposition_eq_scalar l Ω f g P L hP
  simp only [eR]
  unfold GeneralAlgebraicallyClosedCoefficients.ofHom
  apply congrArg (StageSystem.PairCategory.mkHom
      (X := commonStagePullbackObject l Ω (f ≫ g) P)
      (Y := commonStagePullbackObject l Ω f (commonStagePullbackObject l Ω g P)) L hP hP)
  have hfg := commonStagePullbackComparison_eq_transport l Ω (f ≫ g) P L hP eX eZ
  have hg := commonStagePullbackComparison_eq_transport l Ω g P L hP eY eZ
  have hf := commonStagePullbackComparison_eq_transport l Ω f
    (commonStagePullbackObject l Ω g P) L hP eX eY
  have h := stage_transport_of_comparisons
    (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
    _ _ hfg hg hf key
  exact h


/-- The selected common-stage component is represented at every larger coefficient stage.
Source: Stacks 099N(5), coefficient-compatibility argument in residue-compatible pullback.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative).
This is the scalar-extension transport of the chosen integral compositor; it is the
finite-stage calculation used by the naturality proof.
Proof: by the object representation both sides are arrows of the pair category between the
same literal objects. The left side is represented at `P.stage` by the localized integral
compositor at `P.stage`, i.e. by the fixed-stage rational compositor. Enlarging that
representative to `L` applies the coefficient transition `P.stage ≤ L`
(StageSystem.ι_map_eq). The recorded transitions are the rational scalar extensions, and
rationalPullbackComposition_scalar_transport (from integralPullbackComposition_scalar: the
compositor is pinned by its system-level reduction, on which scalar extension acts
compatibly) carries the `P.stage` compositor to the `L` compositor conjugated by exactly the
three `commonStagePullbackComparison` factors; the literal equality transports cancel by
proof irrelevance. -/
theorem commonStagePullbackCompComponent_stage_representation
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (hP : P.stage ≤ L) :
    HEq (commonStagePullbackCompComponent l Ω f g P).hom
      (GeneralAlgebraicallyClosedCoefficients.ofHom
        (commonStagePullbackObject l Ω (f ≫ g) P)
        (commonStagePullbackObject l Ω f
          (commonStagePullbackObject l Ω g P)) L hP hP
        ((commonStagePullbackComparison l Ω (f ≫ g) P L hP).hom ≫
          (commonStagePullbackRationalComposition l Ω f g L P hP).hom ≫
          (rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
            ((commonStagePullbackComparison l Ω g P L hP).inv) ≫
          (commonStagePullbackComparison l Ω f
            (commonStagePullbackObject l Ω g P) L hP).inv)) := by
  have h0 := commonStagePullbackCompComponent_heq l Ω f g P
  have hw := rationalPullbackCompositionIso_heq l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f g P.obj
  have eA : (sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) X).obj
        ((constructibleIntegralPullback l _ (f ≫ g)).obj P.obj.obj) =
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) (f ≫ g)).obj P.obj := by
    simpa only [rationalDerivedPullback] using ((rationalDerivedPullback_existsUnique l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) (f ≫ g)).exists.choose_spec.2.1
        P.obj).symm
  have eB : (sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) X).obj
        ((constructibleIntegralPullback l _ f).obj
          ((constructibleIntegralPullback l _ g).obj P.obj.obj)) =
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).obj
          ((rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) g).obj P.obj) := by
    simpa only [rationalDerivedPullback] using
      ((congrArg (rationalDerivedPullback_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).exists.choose.obj
      ((rationalDerivedPullback_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) g).exists.choose_spec.2.1
          P.obj)).trans
      ((rationalDerivedPullback_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f).exists.choose_spec.2.1
        ((sfRationalConstructibleLocalization l _ Y).obj
          ((constructibleIntegralPullback l _ g).obj P.obj.obj)))).symm
  have h1 := normalization_map_heq
    (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) P.stage)
    eA eB hw.symm
  exact h0.trans (h1.trans (heq_of_eq
    (commonStagePullbackCompComponent_stage_transport l Ω f g P L hP)))

end WeilConjectures
