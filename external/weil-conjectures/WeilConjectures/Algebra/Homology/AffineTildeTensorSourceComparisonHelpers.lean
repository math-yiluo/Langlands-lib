/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit
import WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-! # Counit-normalized affine derived tensor source

Source: Stacks Project, Tags 06Y6, 08DW and 06Z0.
(blueprint: lem-pc-affine-tilde-tensor-source-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

@[reducible]
local instance (priority := 2000) helperSourceCoordinatesCategory (Y : Scheme.{u}) :
    Category Y.Modules := SheafOfModules.instCategory (R := Y.ringCatSheaf)
@[reducible]
local instance (priority := 2000) helperSourceCoordinatesPreadditive (Y : Scheme.{u}) :
    Preadditive Y.Modules := SheafOfModules.instPreadditive Y.ringCatSheaf
@[reducible]
local instance (priority := 2000) helperSourceCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))


local instance helperSourceComparisonTildeAdditive (C : Type u) [CommRing C] :
    (affinePushforwardTilde C).Additive := by
  constructor
  intro M N f g
  exact tilde.map_add (R := .of C) f g
local instance helperSourceComparisonTildeHomology (C : Type u) [CommRing C] :
    (affinePushforwardTilde C).PreservesHomology := tilde_preservesHomology C
local instance helperSourceComparisonTildeLimits (C : Type u) [CommRing C] :
    PreservesFiniteLimits (affinePushforwardTilde C) :=
  (affinePushforwardTilde C).preservesFiniteLimits_of_preservesHomology
local instance helperSourceComparisonTildeColimits (C : Type u) [CommRing C] :
    PreservesFiniteColimits (affinePushforwardTilde C) :=
  (affinePushforwardTilde C).preservesFiniteColimits_of_preservesHomology

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

local instance helperSourceComparisonPullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive :=
  SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f

attribute [local irreducible] tilde tilde.functor Functor.mapDerivedCategory
  affineTildePushforwardComparison Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Scheme.Modules.tensorPullback schemeDerivedBaseChangeMap moduleHomotopyBaseChange

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem quotient_map_Qh {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {P N : CochainComplex C ℤ} (s : P ⟶ N) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map s) =
      DerivedCategory.Q.map s := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality s
  have hi : ∀ K, (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := fun _ ↦ rfl
  rw [hi, hi] at h
  exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
theorem leftCounit_naturality
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    {P N : CochainComplex C ℤ} (s : P ⟶ N) :
    L.map (DerivedCategory.Q.map s) ≫
        cast (by rfl) (ε.app ((HomotopyCategory.quotient _ _).obj N)) =
      cast (by rfl) (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map s) := by
  calc
    _ = L.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map s)) ≫
        ε.app ((HomotopyCategory.quotient _ _).obj N) :=
      congrArg (fun z ↦ L.map z ≫ ε.app ((HomotopyCategory.quotient _ _).obj N))
        (quotient_map_Qh s).symm
    _ = ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quotient _ _).map s)) :=
      ε.naturality ((HomotopyCategory.quotient _ _).map s)
    _ = _ := congrArg (fun z ↦ ε.app ((HomotopyCategory.quotient _ _).obj P) ≫ z)
      (quotient_map_Qh ((F.mapHomologicalComplex (.up ℤ)).map s))

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem normalized_iso_of_resolution
    {C D : Type*} [Category C] [Category D]
    (F G J : C ⥤ D) (a : F ⟶ J) (b : G ⟶ J)
    {P N : C} (s : P ⟶ N) [IsIso (F.map s)] [IsIso (G.map s)]
    [IsIso (a.app P)] [IsIso (b.app P)] :
    ∃ e : F.obj N ≅ G.obj N, e.hom ≫ b.app N = a.app N := by
  let e := (asIso (F.map s)).symm ≪≫ asIso (a.app P) ≪≫
    (asIso (b.app P)).symm ≪≫ asIso (G.map s)
  refine ⟨e, ?_⟩
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  simp only [Category.assoc]
  rw [b.naturality,
    IsIso.inv_hom_id_assoc, ← a.naturality, IsIso.inv_hom_id_assoc]

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
theorem leftDerived_comparison_on_resolution
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    (TR : C ⥤ D) (T : C' ⥤ D') (E : C ⥤ C') (PB : D ⥤ D')
    [TR.Additive] [T.Additive] [E.Additive] [PB.Additive] [(E ⋙ T).Additive]
    [PreservesFiniteLimits TR] [PreservesFiniteColimits TR]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (L : DerivedCategory C ⥤ DerivedCategory C')
    (Lg : DerivedCategory D ⥤ DerivedCategory D')
    (ε : DerivedCategory.Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εg : DerivedCategory.Qh ⋙ Lg ⟶ PB.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (θ : TR ⋙ PB ≅ E ⋙ T)
    {P N : CochainComplex C ℤ} (s : P ⟶ N) [QuasiIso s]
    [hεP : IsIso (ε.app ((HomotopyCategory.quotient _ _).obj P))]
    [hεgP : IsIso (εg.app ((HomotopyCategory.quotient _ _).obj
      ((TR.mapHomologicalComplex (.up ℤ)).obj P)))] :
    let δ := (Functor.mapHomologicalComplexCompIso θ (.up ℤ)).app N
    ∃ e : T.mapDerivedCategory.obj
        (L.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj N))) ≅
      Lg.obj (DerivedCategory.Q.obj ((TR.mapHomologicalComplex (.up ℤ)).obj N)),
      e.hom ≫ cast (by rfl) (εg.app
          ((HomotopyCategory.quotient _ _).obj ((TR.mapHomologicalComplex (.up ℤ)).obj N))) ≫
        DerivedCategory.Q.map δ.hom =
      T.mapDerivedCategory.map (cast (by rfl)
        (ε.app ((HomotopyCategory.quotient _ _).obj N))) ≫
        (T.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (.up ℤ)).obj N)).hom := by
  dsimp only
  let EC := E.mapHomologicalComplex (.up ℤ)
  let TC := T.mapHomologicalComplex (.up ℤ)
  let RC := TR.mapHomologicalComplex (.up ℤ)
  let q := HomotopyCategory.quotient C (.up ℤ)
  let qs := HomotopyCategory.quotient D (.up ℤ)
  let δ := Functor.mapHomologicalComplexCompIso θ (.up ℤ)
  let F := DerivedCategory.Q ⋙ L ⋙ T.mapDerivedCategory
  let G := RC ⋙ DerivedCategory.Q ⋙ Lg
  let J := EC ⋙ TC ⋙ DerivedCategory.Q
  let a : F ⟶ J :=
    { app := fun K ↦ T.mapDerivedCategory.map (ε.app (q.obj K)) ≫
        (T.mapDerivedCategoryFactors.app (EC.obj K)).hom
      naturality := by
        intro P K s
        have h := leftCounit_naturality E L ε s
        simp only [F, J, Functor.comp_map]
        erw [← T.mapDerivedCategory.map_comp_assoc, h, Functor.map_comp]
        have ht := T.mapDerivedCategoryFactors.hom.naturality (EC.map s)
        dsimp only [Functor.comp_map] at ht
        simp only [Category.assoc]
        erw [ht]
        rfl }
  let b : G ⟶ J :=
    { app := fun K ↦ (εg).app (qs.obj (RC.obj K)) ≫
        DerivedCategory.Q.map (δ.app K).hom
      naturality := by
        intro P K s
        have h := leftCounit_naturality (PB)
          (Lg) (εg) (RC.map s)
        have hd :
            ((PB).mapHomologicalComplex (.up ℤ)).map
                (RC.map s) ≫ (δ.app K).hom =
              (δ.app P).hom ≫ TC.map (EC.map s) := δ.hom.naturality s
        calc
          _ = ((Lg).map (DerivedCategory.Q.map (RC.map s)) ≫
              (εg).app (qs.obj (RC.obj K))) ≫
                DerivedCategory.Q.map (δ.app K).hom := (Category.assoc _ _ _).symm
          _ = ((εg).app (qs.obj (RC.obj P)) ≫
              DerivedCategory.Q.map
                (((PB).mapHomologicalComplex (.up ℤ)).map
                  (RC.map s))) ≫ DerivedCategory.Q.map (δ.app K).hom :=
            congrArg (fun z ↦ z ≫ DerivedCategory.Q.map (δ.app K).hom) h
          _ = (εg).app (qs.obj (RC.obj P)) ≫
              DerivedCategory.Q.map
                (((PB).mapHomologicalComplex (.up ℤ)).map
                  (RC.map s) ≫ (δ.app K).hom) :=
            (Category.assoc _ _ _).trans (congrArg
              (fun z ↦ (εg).app (qs.obj (RC.obj P)) ≫ z)
              (DerivedCategory.Q.map_comp _ _).symm)
          _ = (εg).app (qs.obj (RC.obj P)) ≫
              DerivedCategory.Q.map ((δ.app P).hom ≫ TC.map (EC.map s)) :=
            congrArg (fun z ↦ (εg).app
              (qs.obj (RC.obj P)) ≫ DerivedCategory.Q.map z) hd
          _ = _ := (congrArg
              (fun z ↦ (εg).app (qs.obj (RC.obj P)) ≫ z)
              (DerivedCategory.Q.map_comp _ _)).trans (Category.assoc _ _ _).symm }
  have : IsIso (F.map s) := by
    dsimp only [F, Functor.comp_map]
    infer_instance
  have : IsIso (G.map s) := by
    dsimp only [G, Functor.comp_map]
    infer_instance
  have : IsIso (a.app P) := by
    dsimp only [a]
    infer_instance
  have : IsIso (b.app P) := by
    dsimp only [b]
    infer_instance
  exact normalized_iso_of_resolution F G J a b s

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem normalized_unit_exchange
    {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {N N' : C} {X Y Z T V : D} (e : X ≅ L.obj N) (u : N ⟶ N') [IsIso u]
    (b : L.obj N' ⟶ Y) (a : Y ⟶ Z) (ε : L.obj N ⟶ T)
    (c : X ⟶ V) (o : V ⟶ T) (d : T ⟶ Z)
    (hc : e.hom ≫ ε = c ≫ o) (hb : L.map u ≫ b ≫ a = ε ≫ d) :
    (e ≪≫ L.mapIso (asIso u)).hom ≫ b ≫ a = c ≫ o ≫ d := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Category.assoc]
  rw [hb, ← Category.assoc, hc, Category.assoc]



end AlgebraicGeometry

