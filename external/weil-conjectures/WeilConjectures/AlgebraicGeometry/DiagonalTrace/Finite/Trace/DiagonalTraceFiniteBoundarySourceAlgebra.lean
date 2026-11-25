/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundaryMaps
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceNormalizedRootIso
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientRestriction
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientProjection

/-! # Exact categorical transport for a finite supported boundary -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
  diagonalSingleLimitComparison diagonalExactFunctorExtImage
  diagonalShiftedSingleLimitComparison diagonalCompletedGenerator
  SpTowerClasses.lineModule Coefficients.unitMap
  completedSupportedUnit

@[irreducible] private def finiteCoefficientAbIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) (n : ℕ) :
    (sheafCompose (Scheme.ProEt.topology T)
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (Scheme.purTwistFiniteRing T l n) ≅
      (diagonalForget l T).obj ((diagonalFiniteToPadic l n T).obj
        (geoCartierConstant (diagonalResidue.{u} l n) T)) := by
  let J := Scheme.ProEt.topology T
  let A := diagonalResidue.{u} l n
  letI : J.PreservesSheafification
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  letI : J.PreservesSheafification (forget₂ (ModuleCat.{u + 1} A)
      AddCommGrpCat.{u + 1}) := GrothendieckTopology.instPreservesSheafification _ _
  unfold diagonalForget diagonalFiniteToPadic geoCartierConstant
  exact ((constantCommuteCompose J
    ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).app (CommRingCat.of A)) ≪≫
    ((constantCommuteCompose J (forget₂ (ModuleCat.{u + 1} A)
      AddCommGrpCat.{u + 1})).app (ModuleCat.of A A)).symm

@[irreducible] private def finiteCoefficientIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r) (n : ℕ) :
    (r.F.obj (SpTowerClasses.coefficient T
      (SpTowerClasses.Arings l (ULift.{u} (Padic l)) T))).obj (op n) ≅
      (diagonalFiniteToPadic l n T).obj (geoCartierConstant (diagonalResidue.{u} l n) T) := by
  let b := (k.coefficientForget.app (op n)) ≪≫ finiteCoefficientAbIso l T n
  let f := liftToRestriction l T r _ _ _ b.inv
  have hf : (diagonalForget l T).map f = b.inv := by
    ext U x
    dsimp only [f, liftToRestriction]
    unfold diagonalForget
    rfl
  have : (diagonalForget l T).ReflectsIsomorphisms := by
    unfold diagonalForget
    infer_instance
  have : IsIso ((diagonalForget l T).map f) := by rw [hf]; infer_instance
  have : IsIso f := isIso_of_reflects_iso f (diagonalForget l T)
  exact (asIso f).symm

section CoefficientNormalization

private theorem constantCommute_unit'
    {C D B : Type*} [Category C] [Category D] [Category B]
    (J : GrothendieckTopology C) (U : D ⥤ B)
    [HasWeakSheafify J D] [HasWeakSheafify J B]
    [J.HasSheafCompose U] [J.PreservesSheafification U] (A : D) :
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) U ≫
        ((constantCommuteCompose J U).hom.app A).hom =
      (Functor.constComp Cᵒᵖ A U).hom ≫
        toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj A)) := by
  rw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
    sheafComposeIso_inv_fac, ← toSheafify_naturality]

private theorem finiteCoefficientAbIso_one (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (n : ℕ) (U : T.ProEtᵒᵖ) :
    (finiteCoefficientAbIso l T n).hom.hom.app U
        (1 : (Scheme.purTwistFiniteRing T l n).obj.obj U) =
      (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n)))).app U
            (1 : diagonalResidue.{u} l n) := by
  let J := Scheme.ProEt.topology T
  let A := diagonalResidue.{u} l n
  let : J.PreservesSheafification
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let : J.PreservesSheafification (forget₂ (ModuleCat.{u + 1} A)
      AddCommGrpCat.{u + 1}) := GrothendieckTopology.instPreservesSheafification _ _
  let b := (constantCommuteCompose J
    ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).app (CommRingCat.of A)
  let d := (constantCommuteCompose J (forget₂ (ModuleCat.{u + 1} A)
    AddCommGrpCat.{u + 1})).app (ModuleCat.of A A)
  have hb := congrArg (fun t ↦ t.app U (1 : A))
    (constantCommute_unit' J
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) (CommRingCat.of A))
  have hd := congrArg (fun t ↦ t.app U (1 : A))
    (constantCommute_unit' J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
      (ModuleCat.of A A))
  change b.hom.hom.app U
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).app U 1) =
    (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app U (1 : A) at hb
  rw [map_one] at hb
  change d.hom.hom.app U
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A))).app U (1 : A)) =
    (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app U (1 : A) at hd
  unfold finiteCoefficientAbIso
  change d.inv.hom.app U (b.hom.hom.app U
    (1 : (Scheme.purTwistFiniteRing T l n).obj.obj U)) = _
  rw [hb, ← hd]
  exact congrArg (fun f ↦ f.hom.app U
    ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A))).app U (1 : A)))
      d.hom_inv_id

private theorem finiteCoefficientIso_forget (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r) (n : ℕ) :
    (diagonalForget l T).map (finiteCoefficientIso l T c r k n).hom =
      k.coefficientForget.hom.app (op n) ≫ (finiteCoefficientAbIso l T n).hom := by
  let b := (k.coefficientForget.app (op n)) ≪≫ finiteCoefficientAbIso l T n
  let f := liftToRestriction l T r _ _ _ b.inv
  have hf : (diagonalForget l T).map f = b.inv := by
    ext U x
    dsimp only [f, liftToRestriction]
    unfold diagonalForget
    rfl
  apply (cancel_mono b.inv).mp
  change (diagonalForget l T).map (finiteCoefficientIso l T c r k n).hom ≫ b.inv =
    b.hom ≫ b.inv
  have hfi : (finiteCoefficientIso l T c r k n).inv = f := by
    unfold finiteCoefficientIso
    rfl
  rw [← hfi] at hf
  rw [b.hom_inv_id, ← hf, Iso.hom_inv_id_map]
  rfl

private theorem finiteCoefficientIso_one (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r) (n : ℕ)
    (U : T.ProEtᵒᵖ)
    (x : ((r.F.obj (SpTowerClasses.coefficient T
      (SpTowerClasses.Arings l (ULift.{u} (Padic l)) T))).obj (op n)).obj.obj U)
    (hx : HEq x (1 : (SpTowerClasses.systemRing l (ULift.{u} (Padic l)) T).obj.obj
      (op (n, U.unop)))) :
    HEq ((finiteCoefficientIso l T c r k n).hom.hom.app U x)
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n)))).app U
            (1 : diagonalResidue.{u} l n)) := by
  have h := congrArg (fun f ↦ f.hom.app U x) (finiteCoefficientIso_forget l T c r k n)
  have h' : (finiteCoefficientIso l T c r k n).hom.hom.app U x =
      (finiteCoefficientAbIso l T n).hom.hom.app U
        ((k.coefficientForget.hom.app (op n)).hom.app U x) := by
    exact h
  rw [h', k.coefficient_one n U x hx, finiteCoefficientAbIso_one]

private theorem finiteCoefficientIso_one_of_forget (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r) (n : ℕ)
    (U : T.ProEtᵒᵖ)
    (x : ((r.F.obj (SpTowerClasses.coefficient T
      (SpTowerClasses.Arings l (ULift.{u} (Padic l)) T))).obj (op n)).obj.obj U)
    (hx : (k.coefficientForget.hom.app (op n)).hom.app U x =
      (1 : (Scheme.purTwistFiniteRing T l n).obj.obj U)) :
    HEq ((finiteCoefficientIso l T c r k n).hom.hom.app U x)
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n)))).app U
            (1 : diagonalResidue.{u} l n)) := by
  have h := congrArg (fun f ↦ f.hom.app U x) (finiteCoefficientIso_forget l T c r k n)
  have h' : (finiteCoefficientIso l T c r k n).hom.hom.app U x =
      (finiteCoefficientAbIso l T n).hom.hom.app U
        ((k.coefficientForget.hom.app (op n)).hom.app U x) := by
    exact h
  rw [h', hx, finiteCoefficientAbIso_one]

end CoefficientNormalization

private theorem ordinarySourceGeneratorNormalization
    {A B : Type*} [Category A] [Category B] (G : A ⥤ B)
    {I : B} {P Q R S : A} (gamma : I ⟶ G.obj P) (delta : I ⟶ G.obj R)
    (s : P ⟶ Q) (p : R ⟶ Q) (sigma : Q ⟶ S)
    (h : gamma ≫ G.map s = delta ≫ G.map p)
    {Z : Type*} (z : Z) (hsigma : HEq (delta ≫ G.map (p ≫ sigma)) z) :
    HEq (gamma ≫ G.map (s ≫ sigma)) z := by
  have hh : gamma ≫ G.map (s ≫ sigma) = delta ≫ G.map (p ≫ sigma) := by
    simp only [Functor.map_comp, ← Category.assoc]
    rw [h]
  exact (heq_of_eq hh).trans hsigma

private theorem normalizedFiniteClass_hom
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasExt A] [HasExt B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S H : A} (xi : Ext S H 2) {P Q : B}
    (s : F.obj S ≅ P) (t : F.obj H ≅ Q) (z : Ext P Q 2)
    (h : (Ext.mk₀ s.inv).comp
      ((xi.mapExactFunctor F).comp (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2) = z) :
    (DerivedCategory.singleFunctor B 0).map s.inv ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app S ≫
      F.mapDerivedCategory.map xi.hom ≫
      (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app H)⟦(2 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor B 0).map t.hom)⟦(2 : ℤ)⟧' = z.hom := by
  have hh := congrArg (fun a : Ext P Q 2 ↦ a.hom) h
  simpa only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    ShiftedHom.comp_mk₀, Ext.mapExactFunctor_hom, ShiftedHom.map,
    Category.assoc, Nat.cast_ofNat] using hh

private theorem rootSystemTransport_finiteCoordinates
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (V : A ⥤ (ℕᵒᵖ ⥤ B)) [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (W : A) {H : ℕᵒᵖ ⥤ B} {J : DerivedCategory (ℕᵒᵖ ⥤ B)}
    (b : J ≅ ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (e : H ≅ V.obj W) (n : ℕ) {Q : B} (t : H.obj (op n) ≅ Q) :
    ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map
        (rootSystemTransport V W b e).hom ≫
      (supportedFiniteShiftedCoordinates V W n ((e.symm.app (op n)) ≪≫ t)).hom =
    ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map b.hom ≫
      ((((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory).commShiftIso
        (2 : ℤ)).hom.app _ ≫
      ((((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).hom.app H)⟦
        (2 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor B 0).map t.hom)⟦(2 : ℤ)⟧' := by
  simp only [rootSystemTransport, supportedFiniteShiftedCoordinates,
    supportedFiniteSingleCoordinates, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  have hc₀ := Iso.inv_hom_id_map
    ((V.mapDerivedCategory.commShiftIso (2 : ℤ)).app
      ((DerivedCategory.singleFunctor A 0).obj W))
    (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory)
  simp only [Iso.app_inv, Iso.app_hom] at hc₀
  erw [reassoc_of% hc₀]
  erw [Functor.commShiftIso_hom_naturality_assoc]
  let E := ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory
  have hc : (E.map ((V.mapDerivedCategorySingleFunctor 0).inv.app W))⟦(2 : ℤ)⟧' ≫
      (E.map ((V.mapDerivedCategorySingleFunctor 0).hom.app W))⟦(2 : ℤ)⟧' = 𝟙 _ := by
    have hc₁ := Iso.inv_hom_id_map ((V.mapDerivedCategorySingleFunctor 0).app W) E
    simp only [Iso.app_inv, Iso.app_hom] at hc₁
    rw [← Functor.map_comp, hc₁, CategoryTheory.Functor.map_id]
  rw [reassoc_of% hc]
  erw [Functor.commShiftIso_hom_naturality_assoc]
  let hn := ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0
  have hn₀ := hn.hom.naturality e.hom
  simp only [Functor.comp_map] at hn₀
  have hn' := congrArg ((shiftFunctor (DerivedCategory B) (2 : ℤ)).map) hn₀
  simp only [hn, Functor.map_comp] at hn'
  erw [reassoc_of% hn']
  have hc₂ :
      (DerivedCategory.singleFunctor B 0).map
          (((evaluation ℕᵒᵖ B).obj (op n)).map e.hom) ≫
        (DerivedCategory.singleFunctor B 0).map (e.inv.app (op n)) = 𝟙 _ := by
    change (DerivedCategory.singleFunctor B 0).map (e.hom.app (op n)) ≫ _ = _
    rw [← Functor.map_comp, e.hom_inv_id_app, CategoryTheory.Functor.map_id]
    rfl
  have hc₃ := congrArg ((shiftFunctor (DerivedCategory B) (2 : ℤ)).map) hc₂
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id] at hc₃
  erw [reassoc_of% hc₃]

private theorem ordinaryRlim_projection_inv
    {B : Type*} [Category B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (L : DiagonalRlim B) (S : ℕᵒᵖ ⥤ B) (n : ℕ) :
    diagonalOrdinaryRlim L S ≫ (L.projection n).app _ =
      (DerivedCategory.singleFunctor B 0).map (limit.π S (op n)) ≫
        (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).inv.app S := by
  apply (cancel_mono
    ((((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).hom.app S)).mp
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  exact (ordinaryRlim_projection L S n).trans (Category.comp_id _).symm

private theorem projectedPresentedArrow
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasLimitsOfShape ℕᵒᵖ B]
    [HasExt (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (V : C ⥤ (ℕᵒᵖ ⥤ B)) [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {M P : A} (g : M ⟶ P) {S H : ℕᵒᵖ ⥤ B}
    (xi : Ext S H 2) (p : ExtDerivedPresentation S H) (hp : p.Presents xi)
    (s : F.obj P ≅ limit S) (L : DiagonalRlim B)
    (W : C) (e : H ≅ V.obj W) (n : ℕ) {Q : B} (t : H.obj (op n) ≅ Q) :
    F.mapDerivedCategory.map ((DerivedCategory.singleFunctor A 0).map g) ≫
      extSourceComparison F P p s L ≫ (L.projection n).app p.K ≫
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map p.arrow ≫
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map
        (rootSystemTransport V W p.target e).hom ≫
      (supportedFiniteShiftedCoordinates V W n ((e.symm.app (op n)) ≪≫ t)).hom =
    (F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor B 0).map
        (F.map g ≫ s.hom ≫ limit.π S (op n)) ≫
      (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).inv.app S ≫
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map xi.hom ≫
      ((((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory).commShiftIso
        (2 : ℤ)).hom.app _ ≫
      ((((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).hom.app H)⟦
        (2 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor B 0).map t.hom)⟦(2 : ℤ)⟧' := by
  have hp' : xi.hom = p.source.inv ≫ p.arrow ≫ p.target.hom := by
    simpa only [ExtDerivedPresentation.Presents, ExtArrowPresentation] using hp
  simp only [rootSystemTransport_finiteCoordinates]
  unfold extSourceComparison diagonalSingleLimitComparison
  simp only [Category.assoc]
  rw [(L.projection n).naturality_assoc]
  simp only [← Functor.map_comp_assoc]
  rw [← hp']
  rw [reassoc_of% (ordinaryRlim_projection_inv L S n)]
  erw [(F.mapDerivedCategorySingleFunctor 0).hom.naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]

/-- The finite coefficient input followed by the fixed finite arrow and line coordinates.
Source: diagonal trace proof (2), finite Cartier composite.
(blueprint: def-sfb-diagonal-trace-finite-coordinate-map). -/
@[irreducible] def finiteBoundaryCoordinateMap
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (V : C ⥤ (ℕᵒᵖ ⥤ B)) [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : DiagonalRlim B) (M : A) (N W : C) (n : ℕ) {Q R T : B}
    (alpha : (V.obj N).obj (op n) ≅ Q)
    (q : (Functor.const ℕᵒᵖ).obj (F.obj M) ⟶ V.obj N)
    (unit : Q ⟶ R)
    (delta : (DerivedCategory.singleFunctor B 0).obj R ⟶
      ((DerivedCategory.singleFunctor B 0).obj T)⟦(2 : ℤ)⟧)
    (b : (V.obj W).obj (op n) ≅ T) :=
  (exactConeComparison F V L M N q ≫ (L.projection n).app _) ≫
    (supportedFiniteSingleCoordinates V N n alpha).hom ≫
    (DerivedCategory.singleFunctor B 0).map unit ≫ delta ≫
    (supportedFiniteShiftedCoordinates V W n b).inv

/-- The derived finite boundary equation in shared categorical coordinates.
Source: diagonal trace proof (2), finite source projection.
(blueprint: def-sfb-diagonal-trace-finite-boundary-coordinate-equation). -/
@[irreducible] def finiteBoundaryCoordinateEquation
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (V : C ⥤ (ℕᵒᵖ ⥤ B)) [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {M P : A} (g : M ⟶ P) {S H : ℕᵒᵖ ⥤ B}
    (p : ExtDerivedPresentation S H) (s : F.obj P ≅ limit S)
    (L₀ L : DiagonalRlim B) (N W : C) (e : H ≅ V.obj W) (n : ℕ)
    {Q R T : B} (alpha : (V.obj N).obj (op n) ≅ Q)
    (q : (Functor.const ℕᵒᵖ).obj (F.obj M) ⟶ V.obj N) (unit : Q ⟶ R)
    (zHom : (DerivedCategory.singleFunctor B 0).obj R ⟶
      ((DerivedCategory.singleFunctor B 0).obj T)⟦(2 : ℤ)⟧)
    (b : (V.obj W).obj (op n) ≅ T) : Prop :=
    F.mapDerivedCategory.map ((DerivedCategory.singleFunctor A 0).map g) ≫
      extSourceComparison F P p s L₀ ≫ (L₀.projection n).app p.K ≫
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map p.arrow ≫
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map
        (rootSystemTransport V W p.target e).hom =
    finiteBoundaryCoordinateMap F V L M N W n alpha q unit zHom
      b

/-- The evaluated Ext class in the specified finite source and target coordinates.
Source: diagonal trace proof (2), finite Cartier normalization.
(blueprint: def-sfb-diagonal-trace-normalized-finite-ext-class). -/
@[irreducible] def normalizedFiniteExtClass
    {B : Type*} [Category B] [Abelian B] [HasExt B] [HasExt (ℕᵒᵖ ⥤ B)]
    {S H : ℕᵒᵖ ⥤ B} (xi : Ext S H 2) (n : ℕ) {R T : B}
    (sigma : S.obj (op n) ≅ R) (t : H.obj (op n) ≅ T) : Ext R T 2 :=
  (Ext.mk₀ sigma.inv).comp
    ((xi.mapExactFunctor ((evaluation ℕᵒᵖ B).obj (op n))).comp
      (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2)

/-- An ordinary source-unit equation and a normalized evaluated Ext class determine
its finite boundary under arbitrary exact single, shift and limit comparisons.

Source: diagonal trace proof (2), finite source projection.
(blueprint: lem-sfb-diagonal-trace-finite-boundary-from-ordinary-unit).

Proof: cancel the finite target coordinate isomorphism. Naturality of the derived
limit projection moves the source presentation isomorphism next to its inverse.
The presentation equation replaces the represented arrow by the Ext class.
Naturality of the exact shift and single comparisons cancels the root transport
against the target coordinates. The normalized Ext equation is its corresponding
derived Hom equation by Ext.comp_hom and Ext.mapExactFunctor_hom. The ordinary
source equation factors through the normalized source isomorphism inverse, so
this Hom equation applies. The exact-cone projection identity identifies the
remaining coefficient input with its prescribed ordinary projection. -/
theorem diagonalTrace_finiteBoundary_of_ordinaryUnit
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasLimitsOfShape ℕᵒᵖ B]
    [HasExt (ℕᵒᵖ ⥤ B)] [HasExt B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (V : C ⥤ (ℕᵒᵖ ⥤ B)) [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {M P : A} (g : M ⟶ P) {S H : ℕᵒᵖ ⥤ B}
    (xi : Ext S H 2) (p : ExtDerivedPresentation S H) (hp : p.Presents xi)
    (s : F.obj P ≅ limit S) (L₀ L : DiagonalRlim B)
    (N W : C) (e : H ≅ V.obj W) (n : ℕ) {Q R T : B}
    (alpha : (V.obj N).obj (op n) ≅ Q)
    (sigma : S.obj (op n) ≅ R) (t : H.obj (op n) ≅ T)
    (q : (Functor.const ℕᵒᵖ).obj (F.obj M) ⟶ V.obj N)
    (unit : Q ⟶ R) (z : Ext R T 2)
    (hsource : F.map g ≫ s.hom ≫ limit.π S (op n) ≫ sigma.hom =
      q.app (op n) ≫ alpha.hom ≫ unit)
    (hcycle : normalizedFiniteExtClass xi n sigma t = z)
    (zHom : (DerivedCategory.singleFunctor B 0).obj R ⟶
      ((DerivedCategory.singleFunctor B 0).obj T)⟦(2 : ℤ)⟧)
    (hz : z.hom = zHom) :
    finiteBoundaryCoordinateEquation F V g p s L₀ L N W e n alpha q unit zHom
      (e.symm.app (op n) ≪≫ t) := by
  unfold finiteBoundaryCoordinateEquation
  rw [← hz]
  unfold finiteBoundaryCoordinateMap
  have hfactor : F.map g ≫ s.hom ≫ limit.π S (op n) =
      (q.app (op n) ≫ alpha.hom ≫ unit) ≫ sigma.inv := by
    rw [← hsource]
    simp only [Category.assoc, sigma.hom_inv_id, Category.comp_id]
  have hξ := normalizedFiniteClass_hom
    ((evaluation ℕᵒᵖ B).obj (op n)) xi sigma t z
      (by simpa only [normalizedFiniteExtClass] using hcycle)
  apply (cancel_mono
    (supportedFiniteShiftedCoordinates V W n (e.symm.app (op n) ≪≫ t)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [projectedPresentedArrow F V g xi p hp s L₀ W e n t, hfactor]
  simp only [Functor.map_comp, Category.assoc]
  rw [hξ]
  unfold supportedFiniteSingleCoordinates
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [reassoc_of% (diagonalTrace_exactConeComparison_projection F V L M N q n)]

end AlgebraicGeometry.ProEtale.DiagonalTrace
